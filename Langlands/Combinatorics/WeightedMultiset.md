# Multisets of a prescribed additive weight

`WeightedMultiset w n` consists of the multisets with sum of label weights equal to `n`. A weight-preserving equivalence on labels induces an equivalence of these types by mapping the multiset entries. This internal construction can be used with either cuspidal supports or irreducible polynomial factors.

Suppose all weights are positive. If a multiset of weight `n` contains an entry of weight `n`, the remaining entries have total weight zero and hence form the empty multiset. Every other multiset of that weight uses only labels of smaller weight. The equivalence `singletonOrLower` realizes this decomposition as a sum of types.

With finite multiset counts agreeing in all ranks, strong induction compares the numbers of labels of each weight. In the induction step the lower-weight label fibers have the same cardinalities, so their equivalences relabel the multiset types that use just the lower weights. Those terms cancel in the two counts, leaving equality for the labels of the current weight.
