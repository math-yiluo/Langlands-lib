# Proofs for the dimension-shifted subgroup maps

Authors: Worker 45 and Worker 145. Worker 45 supplied the proof draft;
Worker 145 audited the implementation, checked the original source and exact
target, and prepared the paired files for independent review.

The corestriction-after-restriction identity is proved by induction on the
number of coefficient shifts. At degree zero the proof uses the previously
implemented coset-norm calculation. At every other degree, the adjacent
connecting isomorphisms and their inverses cancel. The induction hypothesis
then gives multiplication by the subgroup index, which commutes with the
scalar-linear connecting isomorphism. The integer-degree statement splits
into its nonnegative and negative cases.

All groups involved are Mathlib's actual Tate cohomology groups.
Coefficient naturality is proved by constructing natural transformations
through the functorial coefficient shifts and the natural isomorphisms
given by the actual Tate connecting maps. Component calculations identify
these natural transformations with the recursively defined restriction
and corestriction. Separate lemmas record commutation with the chosen
positive and negative dimension-shift isomorphisms.

This proof uses the published constructions in `TransferDefinitions` and
the degree-zero proof helpers in `ZeroProof`. `TransferLawsProof` assembles
its naturality and index theorems with the scalar-split boundary formulas
from `SplitTransfer` to prove the published `TransferLaws` proposition.
Ordinary comparisons, tower transitivity and cup laws are separate exact
proof obligations. This module does not assert compatibility for arbitrary
nonsplit coefficient sequences.

The dimension-shifting argument is internal, following Serre, *Local Fields*
(1979), Chapter VIII, sections 1–2, printed pp. 127–130 (PDF pp. 133–136),
especially the direct proof of Proposition 4 on p. 130. Registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
