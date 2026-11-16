# Averaging over `O(n)`, simplicity, and reduction to one principal series

Module: `Langlands.Representation.Archimedean.RealSubquotientAverage` (namespace
`Langlands.Archimedean.RealSubquotient`).

This is a helper module for the proof of `RealPrincipalSeriesSubquotientStatement`; see
`RealPrincipalSeriesSubquotientProof.md`. It plays the role of Wallach, *Real Reductive Groups
I*, Lemma 3.5.3 and Proposition 3.5.4. The `K`-invariant matrices act irreducibly on the
`K`-intertwiners of an irreducible module. Here this is obtained by averaging over the compact
group `O(n)` with Haar measure.

## Continuity of the adjoint action

- `exists_continuous_conjLie`: `Ad(k) x` is a combination of the `1 ⊗ E_pq` whose coefficients
  depend continuously on `k ∈ O(n)`.
- `continuous_apply_envMap`: `k ↦ Λ(Ad(k) u)` is continuous for every `u ∈ U(𝔤)` and every
  linear functional `Λ`. The proof is by induction over words, using
  `exists_continuous_conjLie` for the first letter. Every `u` is in the span of words
  (`degreeFiltration_le_wordSpan`).
- `AdU k = envMap (conjLie (orthUnit k))` is the adjoint action on `U(𝔤)`, with `AdU_mul`.

## The `O(n)`-action on matrices

- `kstar τ k c = τ(k⁻¹)ᵀ · Ad(k)(c) · τ(k)ᵀ`. It is an action (`kstar_mul`), linear
  (`kstar_add`, `kstar_smul`), and given entrywise by `kstar_apply`.
- `mem_Bsub_of_kstar`: matrices fixed by every `kstar τ k` are `K`-invariant.
- `act_kstar`: if `ρ(k) P(u) = P(Ad(k) u) ρ(k)` and `c · γ = γ'` for `K`-intertwiners `γ`, `γ'`,
  then `(kstar τ k c) · γ = γ'` for every `k`.
- `kstar_mem`: `kstar` preserves matrices with entries in `U_N`. `continuous_apply_kstar`: for
  continuous `τ`, `k ↦ Λ(kstar τ k c)` is continuous for every linear functional `Λ`.

## Haar averaging

- `matW d N` is the finite-dimensional space of matrices with entries in `U_N`. `exists_level`:
  every matrix lies in some `matW d N`.
- `haarO n = Measure.haar` on `Matrix.unitaryGroup (Fin n) ℝ`, a finite measure.
- `coordExt`, `eq_sum_coordExt`: coordinate functionals of a basis of `matW d N`, extended to
  all matrices.
- `avg τ c = μ(O(n))⁻¹ ∑ᵢ (∫ coordᵢ(kstar τ k c) dk) bᵢ`. `apply_avg`: for continuous `τ`,
  every linear functional `Φ` satisfies `Φ(avg τ c) = μ(O(n))⁻¹ ∫ Φ(kstar τ k c) dk`.
- `act_avg` (**averaging**): if `c · γ = γ'` for `K`-intertwiners `γ`, `γ'` in any module with
  `ρ(k) P(u) = P(Ad(k) u) ρ(k)`, then `avg τ c · γ = γ'`. Test both sides against linear
  functionals of the module and use `act_kstar`.
- `avg_mem_Bsub`: `avg τ c` is `K`-invariant, by left invariance of Haar measure.

## Simplicity and reduction to one principal series

- `act_one`, `act_zero_right`, `PhiT_apply`, `apply_mem_range_PhiT`, `act_smul`.
- `exists_act_eq_of_irreducible` (**simplicity**): in an irreducible
  `(𝔤𝔩_n(ℝ), O(n))`-module `V`, let `T` be a nonzero `K`-intertwiner from `τ`. Then every linear
  map `T' : ℂ^d → V` equals `c · T` for some matrix `c` over `U(𝔤)`. The range of `Φ_T` is a
  nonzero `(𝔤, K)`-stable subspace, hence all of `V`.
- `exists_single_kill` (**reduction to one principal series**): finitely many linear maps `ω_i`
  (`i ∈ F`) into modules with algebra actions `P i`, and a nonzero `T₀`. Assume
  - every `b ∈ Bsub τ` killing all the `ω_i` kills `T₀`;
  - `T₀` is cyclic: if `b · T₀ ≠ 0` then `(b' b) · T₀ = T₀` for some `b' ∈ Bsub τ`.

  Then there are `i ∈ F` and `c ∈ Bsub τ` such that every `b ∈ Bsub τ` with `b · (c · ω_i) = 0`
  kills `T₀`. The proof is by induction on `F`. Either some `c` kills all `ω_g` for `g` in the
  rest of `F` without killing `T₀`, and then the new index works with `c' = b' c`. Or none does,
  and the induction hypothesis applies to the rest of `F`.
