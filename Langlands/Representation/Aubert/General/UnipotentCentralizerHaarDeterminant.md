# Haar determinants on actual positive/zero intersections

This is an internal deduction by Worker 184 from represented dynamic
centralizers, closed subgroup topology, the smooth affine unipotent Haar
determinant formula, and the actual conjugation action on an intersection.
Its namespace is `Langlands.Aubert.General.RationalPointFamily`.

`centralizingUnipotentCentralizerHaarCharacter` is defined over any topological
field `k`, for an affine group scheme `G`, two cocharacters `chi` and `psi`,
and a homomorphism `iZ : Z ⟶ G` whose all-test range centralizes both.
Equip `G(k)` with the canonical point topology and assume that it is a locally
compact topological group. Assume that the literal subgroup

`(Dynamic.unipotent chi ⊓ Dynamic.centralizer psi).carrier (Over.mk (𝟙 _))`

is closed in `G(k)`. The character is the forward closed-normalizer Haar
character composed with the original rational-point map of `iZ`, restricted
to the normalizer of this subgroup. Its values are positive units `ℝ≥0ˣ`.
This definition requires no representative of the intersection.

`unipotentCentralizerHaarDeterminant` proves the following more specialized
formula. Let `k` be a nonarchimedean local field, let `G` be smooth and affine,
and assume that canonically topologized `G(k)` is locally compact, Hausdorff,
and nonarchimedean. Suppose the all-test range of `chi` centralizes `psi`.
Retain `iZ` and its two centralizer containments, require `Z` to be affine,
and let `iU : U ⟶ G` represent the all-test intersection above. Assume `U` is
affine and give finite Lie coordinates `c : Lie.FiniteCoordinates U d`.
Retain the displayed closedness hypothesis on the literal subgroup.
For every `m : Z(k)`, the Haar character, coerced to `ℝ≥0`, equals

`distribHaarChar k (rationalCharacterEval (a.determinantCharacter c) m)`,

where `a` is the actual action
`Dynamic.centralizingUnipotentCentralizerIntersectionAction chi psi iZ hZ hZ' hU`
on this same `U`. In particular the formula concerns the forward action
`x ↦ iZ(m) * x * iZ(m)⁻¹`, with the determinant evaluated on the original
element `m`. All coordinates and representatives remain explicit hypotheses;
the theorem constructs no finite-coordinate system.

The proof forms the canonical represented centralizer `M = Z(psi)`.
Its affine closed immersion into `G` and the dynamic smoothness theorem give
affineness and smoothness of `M`. The centralizer containment factors `chi`
through `M`; it also factors `iU` and `iZ` through `M`. The restriction
lemmas identify this very `U` with the dynamic unipotent subgroup of `M`,
and identify its centralizing action there with the ambient intersection
action. The dynamic closed-subgroup theorem makes the factored `iU` a closed
immersion, and composition also gives closedness of the original `iU`.

The closed embedding `M(k) → G(k)` supplies local compactness, the Hausdorff
property, and the nonarchimedean group property for `M(k)`. Apply
`smoothAffineCentralizingUnipotentHaarDeterminant` in `M`.
The canonical point subgroup homeomorphisms identify `U(k)` with the internal
unipotent subgroup of `M(k)` and with the literal ambient intersection in
`G(k)`. Their composite intertwines the two forward conjugations by the
unchanged rational-point maps. The Haar transport theorem
`CorrectedFiltration.mulEquivHaarChar_eq_closedNormalizerCharacter`
therefore identifies the two Haar factors; the equality of actual actions
identifies their Lie determinants.

No reductivity, whole-common-Levi character detection, positive/positive
intersection formula, normalized representation comparison, or exact K0
expansion is asserted by this pair.
