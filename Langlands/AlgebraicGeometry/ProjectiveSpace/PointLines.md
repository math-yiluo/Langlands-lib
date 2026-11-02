# Projective lines of actual rational points

For every field `K : Type u` and natural number `n`, `pointLine` sends an actual
scheme morphism `p : Spec K → ProjectiveSpace K n` over `Spec K` to a point of
Mathlib's vector-space projectivization `ℙ K (Fin (n+1) → K)`. It takes the line
of `pointCoordinates`, whose nonzero proof comes from its coordinate equal to
one. No algebraic-closedness hypothesis is used.

`eq_of_pointLine_eq` proves that equal lines imply equality of the actual scheme
morphisms. Equal projectivization points supply a unit relating the normalized
coordinate vectors. With the first vector as common homogeneous coordinates,
the first chart's selected coordinate is one and the second chart's selected
coordinate equals that unit. Both chart algebra maps therefore satisfy the
ratio-times-coordinate identities. The published
`specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq` gives equality of
the actual composites through the two chart open immersions. Their recovered
factorization equalities identify the composites with `p` and `q`. Thus
`pointLine_eq_iff` records an equivalence, and `pointLineEmbedding` packages an
injection from the subtype of actual rational points over the field.

`pointLine_linearForm_mem_iff` says that the actual degree-one polynomial
corresponding to a linear functional `ℓ` belongs to the homogeneous prime of
`p(closedPoint K)` if and only if `ℓ` vanishes on `(pointLine n p hp).rep`.
Mathlib's chosen projectivization representative differs from the normalized
coordinates by a unit. Linearity and the nonzero unit make vanishing invariant
under this change; `RationalCoordinates` supplies the incidence test on the
normalized coordinates.

`projectiveLine_eq_of_linear_vanishing` proves that two projectivization points
with identical linear vanishing tests are equal. Their spanned lines have the
same dual annihilator, and injectivity of the dual-annihilator operation for
vector spaces gives equal submodules. Injectivity of the projectivization-to-
submodule map then gives equal projectivization points. Combining this with
the incidence test and the injection proves `eq_iff_linear_incidence` for the
actual scheme morphisms.

The construction and proofs have internal provenance: they combine the existing
normalized coordinates, published actual affine-chart comparison, and Mathlib's
projectivization and dual-annihilator APIs. No surjectivity, field-extension
naturality, scheme action comparison, torsion hyperplane estimate or moduli
representability is asserted by this unit.
