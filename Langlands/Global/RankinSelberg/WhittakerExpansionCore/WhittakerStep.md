# Summable majorants by induction on the level

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerStep`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. This module finishes half (S) of the
Whittaker expansion (see `Interface`): it proves `WhittakerMajorantsStatement`. The induction
and its constants are internal to this proof and not taken from the literature. They make
precise the usual remark that, in the Fourier expansion along `N_(r+1)`, the Whittaker terms of
a smooth automorphic function decay rapidly in the rational coset parameter.

Notation. `d = [F : ℚ]`. For a rational row `v ∈ F^n`, `‖v‖` is the sup norm of its
archimedean image `EqualAnalytic.rowEmbedding F n v`. `W_f` is `whittaker F r ψ f`.
`diag(γ, I)` is `padRational`. A coset of level `m` is an element
`q ∈ N_m(F) \ GL_m(F)` (`UnipotentRationalCosets F m`), and `q.out` is its chosen
representative. `HeightLE F T e ρ` (from `WhittakerHeights`) says that every entry of `ρ` and
of `ρ⁻¹` has archimedean size at most `T` and becomes integral after multiplication by `e`.

## Section `Rows`

* `rowSize v = 1 + ‖v‖`. It is at least `1` (`one_le_rowSize`, `rowSize_pos`) and bounds the
  size of each entry (`norm_le_rowSize`). Scaling by a positive integer `M` multiplies it by at
  most `M` (`rowSize_natCast_mul_le`). The proof bounds each entry with
  `norm_mixedEmbedding_natCast_mul_le` and uses `1 ≤ M`.
* `rowGamma v` is `rowGL v (rowPivot v)` (from `WhittakerCosets`) when `v ≠ 0`, and `1` for
  the zero row. `rowGamma_cosetRow`: for a coset `q` of level `j + 1`, `rowGamma` of its last
  row `ξ_q` is `cosetGamma q`.
* `rowDen M v` is a denominator `e₁ > 0` with `e₁ ≤ M rowSize(v)^d` such that `rowGamma (v / M)`
  has height at most `(M rowSize(v)^d, e₁)`. It is chosen by `Classical.choose` when such an
  `e₁` exists, and is `1` otherwise. `rowDen_pos` and `rowDen_le` hold in both cases.
* `heightLE_rowDen`: if `v` is a nonzero integral row and `M > 0`, then
  `rowGamma (v / M)` has height at most `(M rowSize(v)^d, rowDen M v)`. Proof: the hypotheses
  of `exists_heightLE_rowGL` hold for `ξ = v / M` (with `M ξ = v` integral, of size at most
  `rowSize v`, and `ξ ≠ 0`). So a suitable `e₁` exists, and `rowDen` picks one.
* `weightedFamily n a β` is the function on `F^n × X` that sends `(v, x)` to
  `rowSize(v)^(-a) β v x` when `v` is an integral row (`EqualAnalytic.IntegralRows F n 1`), and
  to `0` otherwise. `weightedFamily_nonneg`: it is nonnegative when `β` is.
* `summable_weightedFamily` (**lattice summation**). Let `β ≥ 0`, every fibre `β v` summable,
  and `Σ_x β v x ≤ K rowSize(v)^a` for every integral row `v`. If `s > n d`, then
  `weightedFamily n (a + s) β` is summable, with total sum at most
  `K Σ_(v integral) rowSize(v)^(-s)`. Proof: the series `Σ_v rowSize(v)^(-s)` over the integral
  rows converges by `EqualAnalytic.summable_integralRows`. On the fibre of an integral `v` the
  family is `rowSize(v)^(-(a+s)) β v`, with sum at most `K rowSize(v)^(-s)`. Fibres over
  non-integral `v` vanish. So the fibre sums are dominated by a summable function, and
  `summable_prod_of_nonneg` and `Summable.tsum_prod'` give summability and the bound.

## Section `Induction`

Throughout, `V` is a space of functions on `GL_(r+1)(𝔸)` with archimedean derivatives `R`
forming a `WhittakerDecayClass`, `ψ` is a standard additive character, and
`CompactSpace (AdeleQuotient F)` holds.

* `stepHeight r M T v = (r + 1) (M rowSize(v)^d T)`.
* `stepFamily r b c N M T e v x = M^N c T^(2N) Σ_o b_o(stepHeight r M T v, rowDen M v · e, x)`,
  for a finite family `b_o` of functions of the height parameters and of a coset `x`.
* `stepMajorant r j b c N D₀ T e q` is `weightedFamily (j + 1) N (stepFamily … (D₀ e²) T e)`
  evaluated at `(D₀ e² ξ_q, cosetRest q)`, where `ξ_q` is the last row of `q.out`.
* `LevelMajorants V ψ m` (for `m ≤ r`) is the inductive statement. There is an exponent `k`,
  the same for all `f ∈ V`, with the following property. For every `f ∈ V` and compact `C`
  there are `A ≥ 0` and functions `b T e` on the cosets of level `m` such that, for all real
  `T ≥ 1` and integers `e > 0`:
  - `b T e ≥ 0`, `b T e` is summable, and `Σ_q b T e q ≤ A (T e)^k`;
  - `‖W_f(diag(q.out, I) ρ x)‖ ≤ b T e q` for every rational `ρ` of height at most `(T, e)`,
    every coset `q` and every `x ∈ C`.
* `subsingleton_unipotentRationalCosets_zero`: there is a single coset of level `0`.

### Level 0 (`levelMajorants_zero`)

Take `k = 0`. The functions `x ↦ |det x|^(-1)` and `x ↦ |det x|` are continuous, so they are
bounded on `C`, by `H₁` and `H₂` respectively. The `bounded` field of the decay class gives a
bound `B` for `f` on the band `(max H₁ 1)^(-1) ≤ |det| ≤ H₂`. For rational `ρ` and
`q.out`, `|det(diag(q.out, I) ρ x)| = |det x|` (`detNorm_ratPoint`, the product formula). So
`norm_whittaker_le_of_band` bounds `‖W_f(diag(q.out, I) ρ x)‖` by `B` for `x ∈ C`. The
majorant is the constant `max B 0`, and its sum over the single coset is `max B 0 = A`.

### Step from level `j` to `j + 1` (`levelMajorants_succ`, `j < r`)

Let `k` be the exponent at level `j`. Put `s = (j + 1) d + 1` and `N = 2dk + s`. The new
exponent is `2N + 5k`. Fix `f` and a compact `C`.

1. **Data.** `exists_lastRow_decay` with exponent `N` gives `c ≥ 0`, independent of `f`.
   `exists_support_denominator` applied to `f` and its level `L` (field `level`) gives an
   integer `D₀ > 0`. The family `wordFamily N f` is finite and lies in `V`. The induction
   hypothesis at level `j`, applied to each `f_o = wordFamily N f o` and `C`, gives `A_o ≥ 0`
   and majorants `b_o`. Put `SA = Σ_o A_o` and `Z₀ = Σ_(v integral in F^(j+1)) rowSize(v)^(-s)`.
   The new constant is `A' = Z₀ c SA (r+1)^k D₀^N D₀^(2k)`, and the new majorant is
   `stepMajorant r j b c N D₀`.
2. **Fibre bound.** Fix `T ≥ 1`, `e > 0` and put `M = D₀ e²`. For an integral row `v`, write
   `T_v = stepHeight r M T v` and `e_v = rowDen M v · e`. Since `rowDen M v ≤ M rowSize(v)^d`,
   `T_v e_v ≤ (r + 1) M² T e rowSize(v)^(2d)`. The mass bounds of the `b_o` then give
   `Σ_(q') stepFamily(v, q') ≤ K rowSize(v)^(2dk)` with
   `K = M^N c T^(2N) SA ((r + 1) M² T e)^k`.
3. **Summability and total mass.** By `summable_weightedFamily` with `a = 2dk`, the family
   `G = weightedFamily (j + 1) N (stepFamily …)` is summable on `F^(j+1) × cosets_j`, with sum
   at most `K Z₀`. The map `q ↦ (M ξ_q, cosetRest q)` is injective
   (`cosetRow_cosetRest_injective` and `M ≠ 0`), and the new majorant is `G` composed with it.
   So the new majorant is summable and its sum is at most `K Z₀`. Expanding `M = D₀ e²`, this is
   `A' T^(2N+k) e^(2N+5k)`, which is at most `A' (T e)^(2N+5k)` because `T ≥ 1`.
4. **Pointwise bound.** Let `ρ` have height at most `(T, e)`, `q` a coset of level `j + 1`, and
   `x ∈ C`. If `W_f(diag(q.out, I) ρ x) = 0` there is nothing to prove. Otherwise
   `exists_support_denominator` shows that `v = M ξ_q` is integral, and `v ≠ 0`. By
   `heightLE_rowDen` and `rowGamma_cosetRow`, `cosetGamma q = rowGamma(v / M)` has height at most
   `(M rowSize(v)^d, rowDen M v)`. With `HeightLE.pad` and `HeightLE.mul`,
   `diag(cosetGamma q, I) ρ` has height at most `(T_v, e_v)`. By `whittaker_padRational_coset`,
   `W_(f_o)(diag(q.out, I) ρ x) = W_(f_o)(diag(q'.out, I) diag(cosetGamma q, I) ρ x)` with
   `q' = cosetRest q`. So the induction hypothesis bounds it by `b_o(T_v, e_v, q')`. The
   last-row decay gives
   `rowSize(ξ_q)^N ‖W_f(diag(q.out, I) ρ x)‖ ≤ c T^(2N) Σ_o ‖W_(f_o)(diag(q.out, I) ρ x)‖`.
   Since `rowSize(v)^N ≤ M^N rowSize(ξ_q)^N`, it follows that
   `rowSize(v)^N ‖W_f(…)‖ ≤ M^N c T^(2N) Σ_o b_o(T_v, e_v, q') = stepFamily(v, q')`.
   Dividing by `rowSize(v)^N` gives exactly the new majorant at `q`.

### Conclusion

* `levelMajorants`: `LevelMajorants V ψ m` for every `m ≤ r`, by induction on `m` from the two
  lemmas above.
* `hasWhittakerMajorants_of_decayClass`: every `f ∈ V` has the majorants of
  `HasWhittakerMajorants`. Take `b = b 1 1` from `LevelMajorants` at level `j`. The pointwise
  bound at `ρ = 1`, which has height at most `(1, 1)` (`HeightLE.one`), is the required bound.
* `whittakerMajorantsStatement_proof : WhittakerMajorantsStatement F`, under the instance
  `CompactSpace (AdeleQuotient F)`. This is half (S).
