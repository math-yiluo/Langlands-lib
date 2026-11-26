# A compact-finite real standard section with nonzero opposite-cell mass

`RealOppositeNonzeroStatement`: for every rank `r + 1`, every list of real character data
`cs` and every order `L`, there is a vector `f` of the `O(r+1)`-finite standard module
`Automorphic.realStandardKFinite (r + 1) (cs.map RealBlock.character)` such that

* `u ↦ (1 + ‖u - 1‖)^L · f(uᵀ)` is integrable on the upper unipotent group for
  `realEntryLebesgue (r + 1)`, and
* the opposite-cell mass `∫ f(uᵀ) du` has strictly positive real part.

`realOppositeNonzero` proves it.

## Proof

By `realOppositeMoment` choose `m` such that all moment sections `momentSection … m'` with
`m' ≥ m` have the prescribed weighted integrability. The section `F(u) = momentSection … m (uᵀ)`
is continuous and integrable and takes the value one at the identity (`momentSection_one`).
The peak weight `w(u) = (oppositeGramProduct u)⁻¹` is continuous, lies in `[0, 1]`, equals
one at the identity, and off every open neighbourhood of the identity it is bounded by a
constant `c < 1`: by `realOppositeGramBound`, `oppositeGramProduct u ≥ 1 + ‖u - 1‖²`, and
outside a neighbourhood the entry vector has norm at least some `δ > 0`, so `c = (1 + δ²)⁻¹`
works. The Library's peak lemma `exists_pos_integral_pow_of_peak` (module
`ComplexJacquetChamberNonzero`, stated for a general Haar measure) gives `j` with
`0 < Re ∫ F(u) w(u)^j du`. By `momentSection_add_opposite` the integrand is
`momentSection … (m + j) (uᵀ)`, and `f = momentSection … (m + j)` is the required vector
(`momentSection_mem`).

This is the real counterpart of the Library's `ComplexOppositeNonzero`: an internal
construction of the nonzero mass that normalizes the compact averages of
`RealNormalizedCompactAverage`.
