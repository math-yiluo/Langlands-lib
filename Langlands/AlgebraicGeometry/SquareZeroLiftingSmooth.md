# The square-zero lifting criterion for smoothness

For a morphism of schemes `f : X ⟶ Y`,
`HasAffineSquareZeroLifting f` requires a solution to every lifting problem
against `Spec (C ⧸ I) ⟶ Spec C` for a square-zero ideal `I` in a commutative
ring `C`. The lift lies over the prescribed map from `Spec C` to `Y` and
restricts to the given map from `Spec (C ⧸ I)` to `X`. The schemes and test rings lie in
the same arbitrary universe.

`HasAffineSquareZeroLifting.smooth` deduces smoothness under local finite
presentation. The lifting property passes to a base change by the universal
property of the pullback. It passes to an open subscheme of the source
because the square-zero quotient is surjective on spectra, so every lift of
a point in that open subscheme has image in the same open. On affine charts
of the base and of the source, the lifting property is the hypothesis of
`AffineLifting.smooth_of_lifting`. Smoothness is local on both the source and
the target.

`HasAffineSquareZeroLifting.of_smooth` follows from the published
square-zero scheme lift. This internal interface combines the Library's
affine smoothness criterion and smooth lifting theorem.
