# Finiteness of relative linear systems near a proper fibre

For an actual line bundle with finitely many generating global sections, this
internal module defines the induced map between the scheme-theoretic fibres of
the existing relative linear-system morphism. All schemes have arbitrary universe
`u`. The source fibre uses the composite with the projective structure morphism,
which is proved equal to the given family morphism.

If the inverse image in the chosen fibre of every section generation open is
affine, the induced fibre map is affine. Indeed the standard coordinate opens
cover the target fibre and are affine there. The whole inverse image of each
such chart is exactly the fibre generation open of the corresponding section,
by `baseFibreMap_fiberι` and `relativeLinearSystemMap_preimage`.

If the source family is proper, the relative linear-system morphism and its
induced fibre map are proper, using separatedness of relative projective space
and its fibres over their respective bases. The affine fibre map is consequently
finite by Mathlib's proper-and-affine criterion.

Finally `exists_isFinite_relativeLinearSystemMap_restrict` applies the generic
finite-near-a-proper-fibre theorem to give an affine base neighbourhood containing
the chosen point on which the relative linear-system morphism is finite.

The proofs are internal compositions of the existing relative linear-system
inverse-image identity, relative-projective-space chart geometry, properness
cancellation, and `ProperFibreFiniteSpreading`. No section lifting is assumed or
proved here, and this unit leaves the full fibre ampleness spreading target open.
