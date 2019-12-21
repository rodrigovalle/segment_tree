//! segment_tree_rs
//!
//! Use the segment tree datastructure provided by this library to query the
//! list of segments a point belongs to in O(log n) time. Construction by
//! calling ::new() takes O(n log n) space and time.
//
// reference: https://en.wikipedia.org/wiki/Segment_tree#Construction

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq)]
struct Interval {
    start: i32,
    end: i32,
}

impl Interval {
    fn new(start: i32, end: i32) -> Interval {
        if start > end {
            Interval {
                start: end,
                end: start,
            }
        } else {
            Interval { start, end }
        }
    }

    fn contains(&self, rhs: &Interval) -> bool {
        self.start <= rhs.start && rhs.end <= self.end
    }

    fn intersects(&self, rhs: &Interval) -> bool {
        !((self.start <= rhs.start && self.end <= rhs.start)
            || (self.start >= rhs.end && self.end >= rhs.end))
    }

    fn contains_point(&self, pt: i32) -> bool {
        self.start < pt && pt < self.end
    }
}

enum UpdateParent {
    OnlyLeft,
    OnlyRight,
    Either,
}

#[derive(Clone, Debug)]
struct Node {
    interval: Interval,
    segments: Vec<Interval>,
}

impl Default for Node {
    fn default() -> Node {
        Node {
            interval: Interval { start: 0, end: 0 },
            segments: Vec::new(),
        }
    }
}

#[derive(Debug)]
struct SegmentTree {
    // The segment tree is stored as an implicit heap
    tree: Vec<Node>,
}

impl fmt::Display for SegmentTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut level = 0;
        loop {
            let nodes_this_level = 2_usize.pow(level);
            let start = nodes_this_level - 1;
            let end = start + nodes_this_level;
            for node_i in start..end {
                if let Some(node) = self.tree.get(node_i) {
                    write!(
                        f,
                        "({},{})",
                        node.interval.start, node.interval.end
                    );
                } else {
                    return Ok(());
                }
            }
            level += 1;
            write!(f, "\n");
        }
    }
}

impl SegmentTree {
    pub fn new(segments: Vec<Interval>) -> SegmentTree {
        // find elementary intervals
        let mut sorted_points = Vec::with_capacity(2 * segments.len());
        for segment in &segments {
            let Interval { start, end } = segment;
            if let Err(idx) = sorted_points.binary_search(start) {
                sorted_points.insert(idx, *start);
            }
            if let Err(idx) = sorted_points.binary_search(end) {
                sorted_points.insert(idx, *end);
            }
        }

        let mut tree = Self::construct_tree(sorted_points);
        for segment in segments {
            Self::insert(segment, &mut tree, 0);
        }

        SegmentTree { tree }
    }

    // construct a balanced binary tree
    // each leaf represents an interval on the number line
    // n_leaves: an interval between each point and intervals to +/-inf
    // n_internal: # internal nodes in a binary tree is equal to leaves - 1
    fn construct_tree(sorted_points: Vec<i32>) -> Vec<Node> {
        let n_leaves = 2 * sorted_points.len() + 1;
        let n_internal = n_leaves - 1;
        let mut tree = vec![
            Node {
                ..Default::default()
            };
            n_internal + n_leaves
        ];

        // If the leaf nodes are split amongst the two lower levels of a
        // complete binary tree, we start by filling out the level furthest from
        // the root first followed by the level above it. The level furthest
        // from the root starts `split` entries into the array, and we then wrap
        // around at `n_leaves` to start filling in the level above. This
        // maintains the invariant that leaf nodes, when viewed left to right in
        // the resulting binary tree, form partitions of the entire number line
        // in order.
        let split = n_leaves.next_power_of_two() - n_leaves;
        let mut prev: i32 = std::i32::MIN;

        for (i, point) in sorted_points.iter().enumerate() {
            let open_int = Node {
                interval: Interval::new(prev, *point),
                ..Default::default()
            };
            let closed_int = Node {
                interval: Interval::new(*point, *point),
                ..Default::default()
            };
            prev = *point;

            let leaf_index_1 = (split + 2 * i) % n_leaves;
            let leaf_index_2 = (split + 2 * i + 1) % n_leaves;
            tree[n_internal + leaf_index_1] = open_int;
            tree[n_internal + leaf_index_2] = closed_int;

            Self::update_parents(
                &mut tree,
                n_internal + leaf_index_1,
                UpdateParent::Either,
            );
            Self::update_parents(
                &mut tree,
                n_internal + leaf_index_2,
                UpdateParent::Either,
            );
        }

        let open_int = Node {
            interval: Interval::new(prev, std::i32::MAX),
            ..Default::default()
        };

        let leaf_index = (split + 2 * sorted_points.len()) % n_leaves;
        tree[n_internal + leaf_index] = open_int;

        Self::update_parents(
            &mut tree,
            n_internal + leaf_index,
            UpdateParent::Either,
        );

        tree
    }

    // given a child node, recurse up the tree to the root setting intervals
    // appropriately given the child's interval
    //
    // i.e. if the first node is a completely filled out child node, and it is
    // the left child of its parent node, then the parent node will have the
    // child's left interval bound. We can recurse on the parent so long as the
    // parent is the left child of its own parent, stopping as soon as we switch
    // to being the right child. Eventually, we visit and set every node's
    // interval in the tree.
    fn update_parents(tree: &mut Vec<Node>, child_i: usize, opt: UpdateParent) {
        let parent_i = match child_i.checked_sub(1) {
            Some(n) => n / 2,
            None => return, // underflow
        };
        let is_left_child = ((child_i - 1) % 2) == 0;

        match opt {
            UpdateParent::OnlyLeft => {
                if is_left_child {
                    tree[parent_i].interval.start =
                        tree[child_i].interval.start;
                    Self::update_parents(tree, parent_i, opt);
                }
            }
            UpdateParent::OnlyRight => {
                if !is_left_child {
                    tree[parent_i].interval.end = tree[child_i].interval.end;
                    Self::update_parents(tree, parent_i, opt);
                }
            }
            UpdateParent::Either => {
                if is_left_child {
                    tree[parent_i].interval.start =
                        tree[child_i].interval.start;
                    Self::update_parents(
                        tree,
                        parent_i,
                        UpdateParent::OnlyLeft,
                    );
                } else {
                    tree[parent_i].interval.end = tree[child_i].interval.end;
                    Self::update_parents(
                        tree,
                        parent_i,
                        UpdateParent::OnlyRight,
                    );
                }
            }
        }
    }

    fn insert(segment: Interval, tree: &mut Vec<Node>, root: usize) {
        if let Some(node) = tree.get_mut(root) {
            if segment.contains(&node.interval) {
                node.segments.push(segment);
            } else {
                let left_child_i = 2 * root + 1;
                if let Some(left_child) = tree.get(left_child_i) {
                    if segment.intersects(&left_child.interval) {
                        Self::insert(segment, tree, left_child_i);
                    }
                }
                let right_child_i = 2 * root + 2;
                if let Some(right_child) = tree.get(right_child_i) {
                    if segment.intersects(&right_child.interval) {
                        Self::insert(segment, tree, right_child_i);
                    }
                }
            }
        }
    }

    pub fn query(&self, p: i32) -> Vec<Interval> {
        let mut ret = Vec::new();
        Self::_query(p, &self.tree, 0, &mut ret);
        ret
    }

    fn _query(p: i32, tree: &Vec<Node>, root: usize, ret: &mut Vec<Interval>) {
        if let Some(root_node) = tree.get(root) {
            if root_node.interval.contains_point(p) {
                ret.extend_from_slice(&root_node.segments);
                Self::_query(p, tree, 2 * root + 1, ret);
                Self::_query(p, tree, 2 * root + 2, ret);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_one_segment() {
        let interval1 = Interval { start: 0, end: 10 };
        let segments = vec![interval1];
        let tree = SegmentTree::new(segments);

        let q = tree.query(-1);
        assert!(q.is_empty());

        let q = tree.query(1);
        assert!(q.contains(&interval1));
        assert_eq!(q.len(), 1);

        let q = tree.query(11);
        assert!(q.is_empty());
    }

    #[test]
    fn test_four_segments() {
        let interval1 = Interval { start: 0, end: 10 };
        let interval2 = Interval { start: 5, end: 15 };
        let interval3 = Interval { start: 8, end: 20 };
        let interval4 = Interval { start: 40, end: 50 };
        let segments = vec![interval1, interval2, interval3, interval4];
        let tree = SegmentTree::new(segments);

        let q = tree.query(-1);
        assert!(q.is_empty());

        let q = tree.query(1);
        assert_eq!(q.len(), 1);
        assert!(q.contains(&interval1));

        let q = tree.query(6);
        assert_eq!(q.len(), 2);
        assert!(q.contains(&interval1));
        assert!(q.contains(&interval2));

        let q = tree.query(9);
        assert_eq!(q.len(), 3);
        assert!(q.contains(&interval1));
        assert!(q.contains(&interval2));
        assert!(q.contains(&interval3));

        let q = tree.query(11);
        assert_eq!(q.len(), 2);
        assert!(q.contains(&interval2));
        assert!(q.contains(&interval3));

        let q = tree.query(19);
        assert!(q.contains(&interval3));

        let q = tree.query(25);
        assert!(q.is_empty());

        let q = tree.query(45);
        assert!(q.contains(&interval4));
    }
}
