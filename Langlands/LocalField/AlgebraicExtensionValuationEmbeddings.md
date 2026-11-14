# Algebra embeddings preserve normalized extension valuations

Let `F` be a nonarchimedean local field and let `E` and `L` be algebraic
extensions of `F`, with independent universes allowed. Every `F`-algebra
embedding `f : E →ₐ[F] L` preserves the normalized real additive extension
valuation already defined in `AlgebraicExtensionValuation`.

`spectralValuation_algHom` proves preservation of the multiplicative
spectral valuation. The spectral norm is the spectral value of the
minimal polynomial; `minpoly.algHom_eq` identifies that polynomial before
and after the injective algebra homomorphism. Applying the same normalized
negative logarithm gives `algebraicExtensionAddValuation_algHom`. The
normalizing scale is that of the common base field `F` on both sides.

`algebraicExtensionUnitCongruenceHom` is the resulting multiplicative map
between the depth-`r` normalized unit congruence subgroups for every
nonnegative real `r`. Its underlying map is `Units.map f.toMonoidHom`.
The definition uses `map_addValuationUnitFiltration_le` and the proved
valuation identity to check subgroup membership, and inherits the
identity and multiplication laws from the unit map.
`algebraicExtensionUnitCongruenceHom_coe` records this underlying map.

This is an internal consequence of the published normalized valuation
construction, Mathlib's spectral norm definition and minimal polynomial
functoriality. It introduces no new literature assertion or hypothesis
about valuation preservation.
