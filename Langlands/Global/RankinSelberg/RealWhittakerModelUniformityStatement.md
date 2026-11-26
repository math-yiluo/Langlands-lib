# One growth exponent for every real Whittaker coefficient map

`Langlands.Global.RankinSelbergGlobal.RealWhittakerModelUniformityStatement` compares two
coefficient spaces of the real standard modules in the Library.

## The statement

Fix a rank index `r`, a list `ds` of real blocks with `realRank ds = r + 1` and a nonzero real
additive parameter `a`. The statement asserts the inclusion of submodules of the functions on
`GL(r + 1, ℝ)`

```text
realWhittakerModel r ds a ≤ realUniformWhittakerModel r ds a .
```

- `realWhittakerModel r ds a` (module `RealLocalWhittakerModel`) is the span of the ranges of
  all maps `B` from the K-finite standard module `realStandardKFinite (r + 1) ds` that satisfy
  `IsRealWhittakerIntertwiner r ds a B`: left covariance under the upper unipotent group by the
  character `realWhittakerCharacter a`, smoothness, compact equivariance, compatibility with the
  Lie action of the standard module, and polynomial growth
  `‖B f g‖ ≤ C * realMatrixHeight g ^ N`, where `C` and `N` may depend on the source vector `f`.
- `realUniformWhittakerModel r ds a` (module `RealUniformWhittakerModel`) is the span of the
  ranges of the maps that satisfy, in addition, a bound of this form with one exponent `N`
  chosen before all source vectors; the constant may still depend on `f`.

The reverse inclusion is the Library's `RealUniformWhittaker.model_le_model`, so the statement
is equivalent to the equality of the two spaces for lists of the stated rank. The rank hypothesis
is the one used for these spaces throughout the Library, for example in
`RealUniformPrincipalSeriesInclusionStatement`.

## Mathematical origin

This is an internal comparison statement. In H. Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), the Whittaker functions are `W_f(g) = λ(π(g) f)` for a continuous `ψ`-form
`λ` on a Casselman–Wallach representation (author-posted version, p. 4). Such a representation
has moderate growth in Jacquet's sense (p. 3, display (2.1)): for every continuous seminorm `μ`
there are `M` and a continuous seminorm `μ'` with `μ(π(g) v) ≤ ‖g‖_H^M μ'(v)`, where
`‖g‖_H = Tr(g ᵗg) + Tr(g⁻¹ ᵗg⁻¹)`. The Library's `realMatrixHeight` is this function
`‖g‖_H`. Bounding `|λ|` by one continuous seminorm therefore gives
`|W_f(g)| ≤ C_f ‖g‖_H^M` with one exponent `M` for all vectors `f`. This is the growth condition
of the uniform coefficient maps. The coefficient maps of `realWhittakerModel` are required to
have polynomial growth only vector by vector. The statement asserts that this weaker
requirement already gives a common exponent, so that every function of the Library's real
Whittaker coefficient space has the growth that Jacquet's Whittaker functions have.

The integrals of the real ordinary Rankin–Selberg tests in
`Langlands.Global.RankinSelbergGlobal.ArchimedeanOrdinaryNormalizedTests` are taken over
`realWhittakerModel`, while the Library's real normalized-growth statements
(`RealLocalGrowthInterfaces`, `RealLocalCharacterGrowthInterfaces`) are formulated on
`realUniformWhittakerModel`. The statement connects the two families.

This module states the comparison and does not prove it.
