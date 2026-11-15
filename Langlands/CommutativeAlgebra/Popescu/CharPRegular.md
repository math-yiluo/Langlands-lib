# Regularity of powers of regular parameters (for Stacks Lemma 11.4)

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.4
(Tag 07FJ), in `CharPResolutionAssembly`. It proves the regularity facts used in the
justifications of steps (12) and (13) of that proof. All declarations are in the namespace
`Langlands.CommutativeAlgebra.Popescu.CharP`.

The source argues: "any permutation of the sequence `π₁, …, π_d` is a regular sequence"
(Algebra, Lemma 106.3, Tag 00NQ), and then "`γ₁ᵉ, …, γ_tᵉ, γ_{t+1}` is a regular
sequence" (Algebra, Lemma 68.9, Tag 07DV). Here these are taken from the Library
statements `RegularLocalParametersStatement` (00NQ) and `RegularSequencePowersStatement`
(07DV), which the lemmas below receive as hypotheses `h00NQ` and `h07DV`.

## Declarations

- `perm_finRange_filter T i hi`: for `i ∉ T`, the list `[0, …, d − 1]` is a permutation of
  `(elements of T) ++ [i] ++ rest` for some list `rest`
  (`List.filter_append_perm` and `List.perm_cons_erase`).
- `isWeaklyRegular_pow_append h00NQ h07DV x hd hx T i hi e he`. Let `L` be a regular
  local ring and `x : Fin d → L` generate the maximal ideal with
  `d = spanFinrank(𝔪_L)`. Let `i ∉ T` and `e > 0`. Then the list `(xⱼᵉ)_{j ∈ T}, xᵢ` is
  weakly regular.
  **Proof.**
  1. By 00NQ, `x₀, …, x_{d−1}` is regular.
  2. By 07DV with the exponents `εⱼ = e` for `j ∈ T` and `εⱼ = 1` otherwise, so is
     `(xⱼ^{εⱼ})ⱼ`.
  3. All terms lie in `𝔪_L`, so the permutation of `perm_finRange_filter` is again
     weakly regular (`IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`).
  4. Its initial segment is weakly regular (`isWeaklyRegular_append_iff`).
- `ofList_map_filter`: the ideal of the filtered list is `Ideal.span (g '' T)`.
- `mem_of_mul_mem_of_isWeaklyRegular`: if `rs ++ [r]` is weakly regular and
  `r y ∈ (rs)`, then `y ∈ (rs)`.
- `mem_of_mul_mem_span_pow h00NQ h07DV x hd hx e he T i hi y hy`: with `L`, `x` as above
  and any flat `L`-algebra `L'`, the image of `xᵢ` is a nonzerodivisor on
  `L' / (xⱼᵉ : j ∈ T)L'`. The weakly regular sequence of `isWeaklyRegular_pow_append`
  stays weakly regular in `L'` (`IsWeaklyRegular.of_flat`).
  The assembly uses `L' = L = k[y]_𝔭` in step (12) and `L' = Λ_q` in step (13). There
  `Λ_q` is flat over `k[y]_𝔭` by Lemma 11.2. So regularity in `Λ_q` comes by flat
  transfer from `k[y]_𝔭`. The source instead says "`π₁, …, π_d` forms a regular sequence
  in `Λ_q`".
- `ogoma_hyp q p e T i hreg u hu v hv m hm`: the hypothesis of Ogoma's lemma
  (`AnnihilatorStabilizationStatement`, Stacks Lemma 10.1, Tag 07FC) for the element
  `v pᵢ` acting on `M = Λ / ((uⱼ pⱼ)ᵉ : j ∈ T)` with `S = Λ \ q`. Assume:
  - `hreg`: `pᵢ` is a nonzerodivisor on `Λ_q / (pⱼᵉ : j ∈ T)`;
  - `hu`, `hv`: `uⱼ ∉ q` and `v ∉ q`.

  If `s (v pᵢ)² m = 0` in `M` for some `s ∉ q`, then `s' (v pᵢ) m = 0` for some `s' ∉ q`.
  **Proof.** Write `m = y mod J`.
  1. In `Λ_q`, the ideal `JΛ_q` equals `(pⱼᵉ : j ∈ T)Λ_q` because the `uⱼᵉ` become units
     (`span_image_unit_mul`).
  2. `hreg`, applied once to `s v² pᵢ y`, gives `s v² pᵢ y ∈ JΛ_q`.
  3. Clearing denominators (`IsLocalization.mem_map_algebraMap_iff`,
     `IsLocalization.eq_iff_exists`) gives `c, t ∉ q` with
     `c t s v (v pᵢ) y ∈ J`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.4 (Tag 07FJ, printed pp. 28-30,
justifications of steps (12) and (13)) and Lemma 10.1 (Tag 07FC, p. 24). Stacks Project,
Chapter 10 *Commutative Algebra* (`stacks-commutative-algebra-chapter-ed88ff78`), Lemmas
10.106.3 (Tag 00NQ) and 10.68.9 (Tag 07DV).
