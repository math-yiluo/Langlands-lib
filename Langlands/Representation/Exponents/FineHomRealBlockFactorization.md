# Every fine Hom factors through a coarse real block

Author: Worker 526. The namespace is
`Langlands.FineHomRealBlockFactorization`. This internal deduction uses
actual normalized refined second adjointness and its target naturality.
The field and all representation-carrier universes remain independent.

`fineMapFixedByProjector` assumes that the actual inner induction of an
admissible fine datum is its entire selected real central block. An
endomorphism of the admissible coarse target acts identically on that
target's same real block. The conclusion states that its actual refined
opposite Jacquet map fixes every fine Hom into that Jacquet module.

Inverse second adjointness turns a given fine Hom into an actual map
from the inner induction. Intertwiners preserve grouped generalized
central characters, so that map has image in the selected target block.
The endomorphism fixes this image. Target naturality of the same public
adjunction family transfers the equality back to the original fine Hom.
No adjunction equivalence is supplied as a hypothesis.

`jacquetMapComp` proves composition of the actual normalized refined
opposite Jacquet maps on quotient representatives.
`fineHomPostcomposeInjective` applies the preceding fixed-map identity
to the composite of a coarse map and a map back. If that composite fixes
the selected block, postcomposition by the first map is injective on
the entire fine Hom space. The comparison carrier need not be admissible
for this helper.

`fineHomPostcomposeFinrankLe` packages postcomposition as a complex linear
map and, under the stated finite-dimensional target-Hom hypothesis,
obtains the finrank inequality.
`nestedFineHomPostcomposeInjective` supplies the source-block equality
from `InnerInducedCoarseScalar.nestedRealBlockEqTop` at `size * t`. It
retains the actual nested refinements and flatten equality, the original
fine irreducibility, admissibility, unitarizability and positive-root
conditions, and the stated admissibility of the fine twist and target.

This argument treats every actual Hom map and retains generalized
central nilpotents. It does not replace Hom dimension by a composition
factor count or require a fine-support premise on the coarse target.
