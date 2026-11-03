# Properness and affine coordinate charts of relative projective space

This internal module supplies geometric properties of the existing actual
`RelativeProjectiveSpace S n`, for arbitrary `Scheme.{u}` and natural `n`.
It introduces `fiberToIntegral S n s`, the composite of the inclusion of the
scheme-theoretic fibre of `toBase S n` at `s` with `toIntegral S n`.

The structure morphism `toBase S n` is proper. The proof identifies the
polynomial structural map with the published `ProjSpace.π`, uses its properness,
transports the integral base to the terminal scheme, and uses stability of
properness under base change.

If `S` is affine, `toIntegral S n` is affine: it is the base change of the
morphism from the affine scheme `S` to the affine terminal scheme. Thus every
whole standard coordinate open of relative projective space is affine, as the
inverse image of the corresponding affine integral coordinate chart.

For every point `s` of an arbitrary base, `fiberToIntegral S n s` is affine.
The proof pastes the residue-field-fibre pullback square with the defining
relative-projective-space square. The resulting projection is a base change
of the morphism from the affine residue-field spectrum to the terminal scheme.
Consequently the inverse images of the coordinate charts in this actual
scheme-theoretic fibre are affine.

These are internal consequences of the existing relative projective space,
polynomial coordinate-cover proof, published `ProjSpace.isProper_π`, and
Mathlib's pullback and morphism APIs. No external mathematical assertion is
assumed. This unit does not prove section lifting or fibre ampleness spreading.

The structure-map comparison reuses
`ProjectiveSpace.toSpec_eq_projSpace_π` from `ProjectiveSpace.Charts`.
