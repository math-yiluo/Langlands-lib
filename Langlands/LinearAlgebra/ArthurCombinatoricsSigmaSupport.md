# The support of `σ_{P_1}^{P_2}`

Lean module: `Langlands.LinearAlgebra.ArthurCombinatoricsSigmaSupport`. It
imports `Langlands.LinearAlgebra.ArthurCombinatoricsSigma`, changes no
published file and states no new proposition.

It is part of the proof of
`Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` and
proves the conjunct

```lean
theorem Langlands.ArthurCombinatorics.sigmaSupportStatement :
    SigmaSupportStatement.{u}
```

Notation as in `ArthurCombinatoricsSigma.md`: `S = b.support`,
`ϖ_i = weightCoordinate P S i`, `A = cartanBlock P S`, `W = A⁻¹`.

## Auxiliary results

- `levelProjection_eq_self`: `H ↦ H_P` is the identity on
  `𝔞_P^G = rootAnnihilator P Θ`, since every `ϖ^Θ_j` vanishes there.
- `weightCoordinate_eq_zero_of_mem_corootSpan`: for `Θ ⊆ S ⊆ b.support` and
  `k ∈ S \ Θ`, `ϖ^S_k` vanishes on `𝔞_0^P = corootSpan P Θ`, because
  `ϖ^S_k(α_j^∨) = 0` for `j ∈ Θ` (the published `weightCoordinate_coroot`).
- `toCoweightBasis_repr_eq`: the coordinates of `Y` in the coroot basis
  `b.toCoweightBasis` are `ϖ_j(Y)`. Both `b.toCoweightBasis.coord j` and
  `ϖ_j` are linear and agree on the basis vectors `α_l^∨`
  (`Module.Basis.ext`).

## Proofs

**`sigma_eq_zero_or_one`** (Lemma 8.3 (a)): by `sigma_eq`, `σ` is an
`if … then 1 else 0`.

**`sigma_support_bound`** (Lemma 8.3 (b)), with the explicit constant
`c = |S| · K_w · (1 + 2 K_w) · K_a`, where `K_w = ∑_{i,l} W_{il}` and
`K_a = ∑_{l,j} |A_{lj}|`. Let `H₁₂ ∈ 𝔞_{P_1}^{P_2}` (that is,
`rootAnnihilator P Θ₁ ⊓ corootSpan P Θ₂`), `H₂ ∈ 𝔞_{P_2}^G` and
`σ_{Θ₁}^{Θ₂}(H₁₂ + H₂) = 1`. Put `H = H₁₂ + H₂` and `n = ∑_j |ϖ_j(H₁₂)|`.

1. `H` lies in `rootAnnihilator P Θ₁`, so `H_{P_1} = H`, and `sigma_eq` gives
   (i) `α_i(H) > 0` for `i ∈ Θ₂ \ Θ₁`, (ii) `α_i(H) ≤ 0` and (iii)
   `ϖ_i(H) > 0` for `i ∈ S \ Θ₂`.
2. `τ_{Θ₁}^{Θ₂}(H₁₂) = 1`: `(H₁₂)_{P_1} = H₁₂`, and for `i ∈ Θ₂ \ Θ₁`,
   `α_i(H₁₂) = α_i(H) > 0` because `α_i(H₂) = 0`.
3. Writing `H₁₂ = ∑_j ϖ_j(H₁₂) α_j^∨` gives `|α_l(H₁₂)| ≤ K_a n =: V` for
   every `l`.
4. `α_l(H₂) ≤ |α_l(H₁₂)|` for every `l ∈ S`: it is `0` for `l ∈ Θ₂`, and (ii)
   gives `α_l(H₂) ≤ −α_l(H₁₂)` for `l ∉ Θ₂`.
5. For `i ∈ S \ Θ₂`, `ϖ_i(H₁₂) = 0`, so (iii) reads
   `∑_l W_{il} α_l(H₂) > 0`. Put `d_l = |α_l(H₁₂)| − α_l(H₂) ≥ 0`. Since
   `W ≥ 0`,
   `W_{ii} d_i ≤ ∑_l W_{il} d_l < ∑_l W_{il} |α_l(H₁₂)| ≤ K_w V`. As
   `W_{ii} ≥ 1/2` (`half_le_cartanBlock_inv_self`), `d_i ≤ 2 K_w V`, and so
   `|α_i(H₂)| ≤ (1 + 2 K_w) V`. For `i ∈ Θ₂`, `α_i(H₂) = 0`.
6. Each coordinate `ϖ_j(H₂) = ∑_l W_{jl} α_l(H₂)` has absolute value at most
   `K_w (1 + 2 K_w) V`. Summing over the `|S|` coordinates gives
   `∑_j |ϖ_j(H₂)| ≤ c · n`.

**`sigmaSupportStatement`** combines the two for `S = b.support`.

## Provenance

`SigmaSupportStatement` is Arthur, *An introduction to the trace formula*
(2005), Lemma 8.3, §8, p.42 (in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`; PDF page = printed
page + 12, so PDF page 54). Arthur refers its proof to Lemma 6.1 of
*A trace formula for reductive groups I* (1978), registered as
`arthur-1978-trace-formula-reductive-groups-I`. The bound in (b) is the
argument of Corollary 6.2 of the 1978 paper, p.939 (PDF page 29), with
`T = 0`: `α(H₂) ≤ −α(H₁₂)` for the roots outside `Θ₂` and `ϖ(H₂) > 0` confine
`H₂` to a set whose size is bounded by a multiple of the size of `H₁₂`. The
Lean proof makes this explicit in the coroot coordinates. The statement uses
the `ℓ¹` norm in the coroot basis, so no equivalence of norms is needed.

## Axioms

The module compiles without errors or warnings. The
lake-build inspection (over Library `72480b70`) of `arthurCombinatoricsStatement`, which
depends on `sigmaSupportStatement`, reports only `propext`,
`Classical.choice` and `Quot.sound`.
