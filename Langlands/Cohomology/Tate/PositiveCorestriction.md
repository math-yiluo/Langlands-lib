# Positive-degree comparison for corestriction

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The constructed Tate corestriction agrees with the independently defined
ordinary cohomological corestriction in every positive degree. Both maps use
Mathlib's actual cohomology objects, conjugated by its existing Tate comparison
isomorphisms.

The proof first compares the maps from the auxiliary zero splice in all
nonnegative degrees. At degree zero, the previously computed coset-norm
formula agrees with the defining formula for Tate corestriction. For the
induction step, restrict the actual coinduced embedding sequence to the
subgroup. Its middle term has vanishing positive comparison homology, so the
connecting map surjects onto every
positive comparison class. The ordinary-transfer comparison and Tate
corestriction commute with this connecting map, and the induction hypothesis
identifies the source maps. Finally, cancel the positive-degree comparison
isomorphisms.

This is an internal proof of the ordinary-corestriction clause of
`OrdinaryComparisons`, with transfer conventions from Serre, *Local Fields*
(1979), VII section 7, printed pages 118–119, and VIII section 2, printed pages
129–130. Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The scalar ring is any commutative ring and the common carrier universe is
arbitrary. No general short exact sequence is assumed split; the proof uses
the proved scalar splitting of the specific coinduced replacement sequence.
