# Diagonal tori, block unipotents and adelic splittings

Elementary group-theoretic helpers for the rapid-decay argument for cusp forms
(`Langlands.Automorphic.CuspidalL2.Decay`). Provenance: internal. These are
routine matrix and product-group identities, derived directly from the Library's
definitions of `GeneralLinear.blockUnipotent`, `PrimitiveAdelicHeight.diagonalGL`,
`PositiveRealIdeles` and the adelic splitting maps `AdelicGL.infinite`,
`AdelicGL.finite`, `AdelicGL.ofInfinite`, `AdelicGL.ofFinite`.

## Contents

- `GeneralLinear.diagonalGL_inv_mul_blockUnipotent_mul`: for an invertible diagonal
  matrix `d` and a block unipotent `u(X)` along `a + b = n`,
  `d⁻¹ u(X) d = u(X')` with `X' i j = d_{e(inl i)}⁻¹ * X i j * d_{e(inr j)}`, where
  `e = finSumFinEquiv.trans (finCongr h)`. Proof: entrywise computation after
  reindexing by `e`.
- `AdelicGL.ext_infinite_finite`: an adelic element is determined by its infinite
  and finite parts. `infinite_ofInfinite`, `finite_ofInfinite`, `infinite_ofFinite`,
  `finite_ofFinite`: the four projection/inclusion identities.
  `ofInfinite_commute`: infinite and finite inclusions commute.
  `eq_ofInfinite_mul_ofFinite`: `g = ofInfinite (infinite g) * ofFinite (finite g)`.
- `AdelicGL.blockUnipotent_eq`: an adelic block unipotent `u(Y)` is the product of
  the infinite block unipotent with block `Y.map RingHom.fst` and the finite one with
  block `Y.map RingHom.snd` (both parts checked with `GeneralLinear.map_blockUnipotent`).
- The imported `Automorphic.rational_blockUnipotent`: the rational embedding maps a rational block
  unipotent `u(ξ)` to the adelic block unipotent with block `ξ.map (algebraMap K _)`.
- `expUnit x`: `Real.exp x` as a unit of `ℝ≥0`; `coe_expUnit`, `expUnit_add`.
- `torInf K n x`: the infinite adelic diagonal element `diag(e^{x_1}, …, e^{x_n})`,
  built from `PositiveRealIdeles.infinite (expUnit (x i))` (the same positive real at
  every infinite place). `torInf_val`, `torInf_add`, `torInf_zero`, `continuous_torInf`
  record its value, the homomorphism property in `x`, and continuity;
  `positiveRealIdeles_infinite_val`, `positiveRealIdeles_infinite_inv_val` give the
  infinite adele values used there.
- `torInf_inv_mul_blockUnipotent_mul`: conjugating an infinite block unipotent `u(Y)`
  by `torInf x` multiplies the entry `Y i j` by
  `infiniteRealEmbedding (exp (x (e (inr j)) - x (e (inl i))))`; a specialization of
  the diagonal conjugation formula above.
