# Step (13) of Stacks Lemma 11.4, without enlarging `D`

This module supports the proof of Stacks Project, *Smoothing Ring Maps*, Lemma 11.4
(Tag 07FJ), in `CharPResolutionAssembly`. It proves a variant of step (13) of that proof.
All declarations are in the namespace `Langlands.CommutativeAlgebra.Popescu.CharP`.

**Notation.**
- `Λ` is a Noetherian ring and `q` a prime of `Λ`.
- `Λ_q = Localization.AtPrime q` has maximal ideal `𝔪`.
- `Λ̄ = localTruncation q n = Λ_q/𝔪ⁿ`, and `toLocalTruncation q n : Λ → Λ̄` is the
  canonical map (module `EssentiallySmooth`).
- `ψ : D → Λ̄` is a flat local homomorphism from a local ring `D`. This is the map
  `D → Λ_q/qⁿΛ_q` of step (9), from Lemma 11.2.
- `g : Fin r → Λ` are the images `f(aⱼ)` of generators of `H_{A/k}`.

## Difference from the source

Step (13) of the source produces `δᵢ ∉ q` and an enlargement `D → D'` with three
properties, where `π'ᵢ = δᵢπᵢ`:
- (a) `π'ᵢ^{2N} = Σⱼ aⱼλᵢⱼ` with `λᵢⱼ mod qⁿΛ_q ∈ D'`;
- (b) the annihilator condition for `π'ᵢ` modulo `(π'ⱼᵉ : j < i)`;
- (c) `δᵢ mod qⁿΛ_q ∈ D'`.

The enlargements use Lemma 11.3 (Tag 07FI). The Lean proof needs no enlargement and no
Lemma 11.3. Step (26) only uses the elements `λᵢⱼ/δᵢ^{2N}`. These already lie in the
original `D`, by the choice of `λᵢⱼ` in the justification of step (13): "`µ_{t+1,j}` maps
to `s^{2N}dⱼ`". So the Lean proof records exactly this property:

- `Adm q n N g ψ l x` ("`l` is an admissible multiplier for `x`") holds when there are
  `λ : Fin r → Λ` with
  - `(l x)^{2N} = Σⱼ λⱼ gⱼ` in `Λ`, and
  - for each `j`, some `w ∈ D` with `λⱼ ≡ l^{2N} ψ(w)` in `Λ̄`.
- `Adm.mul`: if `l` is admissible for `x`, so is `s l` for every `s ∈ Λ`. Take
  `s^{2N}λⱼ` and the same `w`.

Property (a) for `π'ᵢ` becomes `Adm(δᵢ, πᵢ)`. Property (c) is not needed.

## Declarations

- `toLocalTruncation_apply`: `toLocalTruncation q n x` is the class of `x/1`.
- `isLocalRing_localTruncation`: `Λ̄` is local for `n > 0`.
- `exists_adm` (the first half of the justification of (13)). Assume:
  - `1 ≤ N ≤ n`;
  - `𝔪^N ⊆ (gⱼ)Λ_q` (from step (1): `q^NΛ_q ⊆ H_{A/k}Λ_q`);
  - the images of the `gⱼ` and of `x` in `Λ̄` lie in the range of `ψ`;
  - `x ∈ q`.

  Then some `l ∉ q` is admissible for `x`.
  **Proof.** This follows the source.
  1. Write `x̄ = ψ(b)`. Then `x^N ∈ (gⱼ)Λ_q`, so `ψ(b^N) ∈ (gⱼ)Λ̄ = (ψ(bⱼ))Λ̄`. Since
     `ψ` is faithfully flat (`comap_map_of_flat_of_isLocalHom`), `b^N = Σⱼ dⱼ bⱼ` in `D`.
  2. Lift `ψ(dⱼ)` to `cⱼ ∈ Λ_q`. Then `ε = x^N − Σⱼ cⱼ gⱼ ∈ 𝔪ⁿ ⊆ 𝔪^{n−N}(gⱼ)`. So
     `ε = Σⱼ c'ⱼ gⱼ` with `c'ⱼ ∈ 𝔪^{n−N}` (`Submodule.mem_ideal_smul_span_iff_exists_sum`).
  3. Put `µ'ⱼ = x^N (cⱼ + c'ⱼ)`. Then `x^{2N} = Σⱼ µ'ⱼ gⱼ` in `Λ_q` and
     `µ'ⱼ ≡ ψ(b^N dⱼ)` in `Λ̄`, because `x^N c'ⱼ ∈ 𝔪ⁿ`.
  4. Clear denominators. Take `s₁ ∉ q` with `s₁µ'ⱼ = µ''ⱼ/1`
     (`IsLocalization.exist_integer_multiples_of_finite`). Take `s₂ ∉ q` with
     `s₂ s₁ x^{2N} = s₂ Σ µ''ⱼ gⱼ` in `Λ` (`IsLocalization.exists_of_eq`).
  5. Then `l = s₁s₂`, `λⱼ = l^{2N−1} s₂ µ''ⱼ` and `wⱼ = b^N dⱼ` work.
- `exists_step13 hOg q hN hNn g hH ψ hψ hg p hpq hp e hreg`. Assume the hypotheses of
  `exists_adm` for each `pᵢ`. Assume also `hreg`: for every `T` and `i ∉ T`, `pᵢ` is a
  nonzerodivisor on `Λ_q / (pⱼᵉ : j ∈ T)`. Then there are `δ : Fin d → Λ` such that:
  - `δᵢ ∉ q` for all `i`;
  - `Adm(δᵢ, pᵢ)` holds for all `i`;
  - for all `i` and `y ∈ Λ`, `(δᵢpᵢ)² y ∈ ((δⱼpⱼ)ᵉ : j < i)` implies
    `δᵢpᵢ y ∈ ((δⱼpⱼ)ᵉ : j < i)`.

  **Proof.**
  1. Take `lᵢ ∉ q` admissible for `pᵢ` (`exists_adm`), for each `i`, before the
     induction.
  2. Induct on `t ≤ d`, starting from `δ = l`. At step `i₀ = t`, apply Ogoma's lemma
     (`AnnihilatorStabilizationStatement`, hypothesis `hOg`) with:
     - the module `Λ / ((δⱼpⱼ)ᵉ : j < i₀)`;
     - the element `δᵢ₀ pᵢ₀`;
     - `S = Λ \ q`.

     Its hypothesis is `ogoma_hyp` (module `CharPRegular`). This gives `σ ∉ q`.
  3. Replace `δᵢ₀` by `σ δᵢ₀`. It is still admissible by `Adm.mul`. The ideals for
     `i < i₀` are unchanged.

In the assembly, `hreg` comes from `mem_of_mul_mem_span_pow` (module `CharPRegular`) by
flat transfer from `k[y]_𝔭` to `Λ_q`. The source instead uses that `π₁, …, π_d` form a
regular system of parameters of `Λ_q`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 11.4 (Tag 07FJ, printed pp. 28-31,
steps (1), (13), (26) and the justification of (13)); Lemma 10.1 (Tag 07FC, p. 24);
Lemma 11.3 (Tag 07FI, p. 27), which the Lean proof does not use.
