# Tensor induction in ordered refinement stages

This internal construction composes published actual representation equivalences.
For shapes `B D`, a refinement `S` of `D`, and exact block-coordinate data
`e`, `hs`, `hc`, `orderedRefinementTensorInductionEquiv` compares the ordinary
normalized product induction of smooth block factors for `B` with normalized
product induction for `D` of their inner normalized product inductions for `S`.

Every original factor is moved to its inner position by `e` and transported
along the exact rank equality `hs`. The auxiliary
`orderedRefinementTensorFactors` forms their smooth external tensor in each
outer block. The resulting equivalence acts on the actual smooth induced
function spaces. The field and factor-carrier universes are independent; the
induced carriers use their natural maximum. No positive-rank, admissibility,
irreducibility or finite-length hypothesis is imposed, and empty families
remain included.

The construction first uses `FiniteTensor.glRefinementEquiv` to identify the
original external tensor, pulled along the inverse concrete Levi-coordinate
equivalence, with the nested tensor on the actual refined Levi. It inflates
this equivalence through the refined Levi projection, twists both sides by the
same canonical positive half of the refined parabolic modulus, and applies
`Induction.smoothInducedEquiv`. The published `refinedInductionTensor` then
identifies this refined induction with the external tensor of the actual
inner normalized inductions. Applying
`T.normalizedParabolicInducedEquiv` lifts their composite to outer induction.
Finally, the inverse of `orderedRefinementInductionEquiv` identifies ordinary
induction of the original tensor with the iterated induction at its source.
Smoothness needed for this last equivalence follows from finite external-tensor
smoothness of the given factors.

The provenance is internal: this module composes the published constructions
in `Tensor.GLRefinement`, `Parabolic.RefinedInductionTensorProof`,
`Induction.Equivalences`, and `Parabolic.OrderedRefinementInduction`.
It establishes a generic comparison of induced representations. It does not
assert factor matching for a swap or finite length of any induction.
