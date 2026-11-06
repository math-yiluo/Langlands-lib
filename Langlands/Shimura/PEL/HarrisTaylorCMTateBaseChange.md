# Actual base change of full Tate-normalized Harris CM models

Author: Worker 344.

This is an internal construction on the existing universe-zero Harris CM
data, the existing prerequisite package, and the full category
`AdmissibleCMBaseCategory` of connected admissible test bases. It additionally
uses the named duality, polarization, finite Weil transition, adelic
comparison and torsion prerequisites already used by the original pullback.
No new source theorem is asserted.

For a morphism `f : Y ⟶ X`, a geometric point `a` of `Y`, and an original
Harris level `U`, `tateNormalizedCMRepresentativeBaseChange` pulls back an
actual `TateNormalizedCMRepresentative` at the pushed point `a.comp f.hom.left`.
It uses `integralCMRepresentativeBaseChange`: thus the target has the actual
pulled-back abelian scheme, polarization, rational action, original level
orbit and integral order action. The original CM determinant and dimension
condition is transported by that existing construction and aligned with the
target structure map using the actual triangle `Over.w f.hom`. The existing
`harrisIntegralLevelCondition_levelDataBaseChange` equivalence proves the
original full integral Tate-image normalization for precisely that pulled-back
level data. No new level representative is selected.

`tateNormalizedCMRepresentativeClass_baseChange` identifies its original CM
class with `geometricFamilyPointPullback`. The proof expresses the aligned
pullback as actual base change between source and target presentation
transports. `classPresentationEq_val_val` removes the structural-map transport
on the underlying ambient class, and both point equalities are reflexive.
The remaining equality is definitional.

`tateNormalizedCMRelated_baseChange` uses the existing equality-of-original-
classes criterion and the last square to preserve the unchanged
rational-isogeny relation. `tateNormalizedCMClassBaseChange` is its
`Quotient.map`. Quotient induction proves `tateNormalizedCMForget_baseChange`,
so forgetting this actual quotient pullback yields exactly the original
CM point pullback, including the structure triangle.

These constructions require no generic lattice realization, existence of
normalized models, or source-stabilizer containment. They work at each
original level; this file makes no assertion that every Harris transporter
preserves full integral normalization. It constructs no representing scheme
and does not prove `DivisionCMRepresentabilityStatement`.
