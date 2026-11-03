# Compatible normalization of generic frame transitions

This internal construction concerns a morphism of actual schemes
`q : Y ⟶ X`, a family of total opens `T i`, overlap units `g i j`
on their inverse images, and a reference index `i₀`.
The family need not cover `X`.

`sectionUnitRestrict` and `sectionUnitPullback` are the group homomorphisms
obtained by mapping units through the actual structure-sheaf restriction
and the original section map `q.app`. Their composition and naturality
lemmas follow by taking unit values and applying presheaf composition and
naturality.

`GenericScalarNormalization` consists of a generic unit `scalar i` on each
inverse-image open and a total unit `totalUnit i` on `T i₀ ∩ T i`.
Its equality requires `g i₀ i` to be the product of the restricted
`scalar i` and the pullback of `totalUnit i`. The structure does not
require that the overlap units form a cocycle or that the units named
`scalar` come from the base.

`GenericScalarNormalization.transition_restrict` adds the cocycle
hypothesis. On any total subopen `W` contained in `T i₀`, `T i`, and
`T j`, the changed transition `scalar i * g i j * (scalar j)⁻¹`,
with the indicated restrictions, is the pullback of
`(totalUnit i|W)⁻¹ * (totalUnit j|W)`.
The implemented proof restricts both reference equalities and the cocycle
identity to `W`, then cancels units in the commutative unit group.

`affineGenericScalarNormalization` constructs this data when `R` is
an arbitrary valuation domain, `K` is the supplied fraction field, and
the square formed by `q`, `s`, and `p : X ⟶ Spec R` is a pullback.
The morphism `p` is smooth and geometrically connected. Each `T i`
and each reference intersection `T i₀ ∩ T i` must be affine; every
reference intersection must meet the closed fibre, and its actual
section algebra must be projective over `R`, using
`affineSectionAlgebra p`.

The constructor applies `affineGenericUnitDecomposition` to each
reference transition. It chooses its two nonzero base scalars and
total unit, then defines `scalar i` using the same scalar ratio on
the larger affine open `T i`. Compatibility of
`affineGenericScalarRatio` with actual restriction gives the required
reference equality.

The provenance is internal: the construction combines the imported
affine scalar decomposition with restriction naturality and commutative
unit-group algebra. Projectivity is an explicit input. This module
does not prove geometric projectivity, lift all changed transitions to
total units, glue a line bundle, or prove the two-axis extension statement.
