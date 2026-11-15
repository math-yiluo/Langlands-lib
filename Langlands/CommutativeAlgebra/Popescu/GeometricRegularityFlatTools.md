# Auxiliary lemmas for the proof of Stacks 07E6

- `injective_of_span_of_linearIndependent`: a linear map is injective if it sends a finite
  spanning family to a linearly independent family.
- `span_one_tmul`: if `u` spans the `A`-module `M`, then the `1 ⊗ u_i` span `K ⊗_A M` over `K`.
- `exists_fin_span_eq_maximalIdeal`: the maximal ideal of a Noetherian local ring is generated
  by a family indexed by `Fin (spanFinrank 𝔪)`. Mathlib's
  `Submodule.FG.exists_span_finset_card_eq_spanFinrank` gives such a finset, which is then
  reindexed.
- `isWeaklyRegular_of_linearIndependent` (hypothesis: `RegularLocalParametersStatement`,
  Stacks 00NQ): in a regular local ring `A`, take elements `f_1, …, f_d ∈ 𝔪` whose classes in
  `𝔪/𝔪²` are linearly independent. They form a weakly regular sequence.
  - Lift a basis of `(𝔪/𝔪²)/⟨f̄⟩` to elements `t_j ∈ 𝔪`. This step is copied from the Library
    proof of `isRegularLocalRing_quotient_span_of_linearIndependent`.
  - Nakayama: the `f_i` and the `t_j` then generate `𝔪`.
  - Their number is `dim 𝔪/𝔪² = spanFinrank 𝔪`, so the family `f ++ t` is a regular sequence
    by 00NQ.
  - Its prefix `f` is weakly regular by `isWeaklyRegular_append_iff`.
- `span_D_localization`: for a prime `𝔭` of `k[y_1, …, y_m]`, the differentials `dy_i` span
  `Ω_{k[y]_𝔭/k}` over `k[y]_𝔭`.
  - The localization is formally étale, so `k[y]_𝔭 ⊗ Ω_{k[y]/k} ≅ Ω_{k[y]_𝔭/k}`
    (`tensorKaehlerEquivOfFormallyEtale`).
  - The `dy_i` form a basis of `Ω_{k[y]/k}` (`mvPolynomialBasis`).
