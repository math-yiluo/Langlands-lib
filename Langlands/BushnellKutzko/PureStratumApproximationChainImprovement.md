# BK93 (2.4.5): improving a simple approximation

Source: Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`, Lemma (2.4.5), printed p. 67 (PDF p. 79), with its proof, printed pp. 67–69 (PDF pp. 79–81).

`chainImprovement : ChainImprovementPremise` proves the Library proposition `ChainImprovementPremise` (module `PureStratumApproximationAssembly`), with the same universes and no further hypothesis. Its statement is described in that module's Markdown: if `S` is simple with `E = F[S.b]` and the derived stratum `D` of `β − S.b` has an element of its coset differing from a scalar of `E` by a nilpotent element, then `β` lies in the coset of a simple stratum `T` with `T.r · e(S) < S.r · e(T)` whose generated field has the ramification index and residue degree of `F[S.b]`.

## Auxiliary results

- `restrictScalars_algebraMap` and `isNilpotent_restrictScalars`: a scalar of `E` acts as `subfieldEmbedding`; restriction of scalars preserves nilpotence.
- `subfieldEmbedding_mem_of_isNilpotent_sub`: if `y ∈ 𝔓^k` and `y − x` is nilpotent for `x ∈ E`, then `x ∈ 𝔓^k`. Otherwise `x` is a unit of shift less than `k`, `x⁻¹y ∈ 𝔓^1`, and `y − x = −x(1 − x⁻¹y)` would be a unit.
- `exists_scalar_simple`: if `x ∈ E` has valuation `−ρ` on a chain `𝓜` normalized by `E`, then `[𝓜_E,ρ,ρ−1,x]` is a simple stratum over `E` on the subfield chain of `𝓜`. Its generated algebra is `⊥ ≅ E`, its units act by elements of `Eˣ`, and its critical exponent is `⊥`.
- `subfieldEmbedding_mem_elementAlgebra` and `adjoin_pair_eq_elementAlgebra`: scalars of `E = F[S.b]` lie in `F[S.b]`, so `F[S.b, x] = F[S.b]` for `x ∈ E`.

## Proof

Write `r = S.r`, `b = β − S.b`, and let `x ∈ E`, `y ∈ D.coset` with `y − x` nilpotent. Then `y − s(b) ∈ 𝔓^{1−r}` and `s(b) ∈ 𝔓^{−r}` (T1), so `y ∈ 𝔓^{−r}`, and `x ∈ 𝔓^{−r}` by the auxiliary result. Apply `exists_compatible_chain_of_isNilpotent` to `z = s(b) − x` and the nilpotent `y − x`. This gives a compatible chain `𝓜` normalized by `E` and `j'` with `z + 𝔓^{1−r}(𝓛) ⊆ 𝔓^{j'}(𝓜)` on `E`-linear maps and `−r e(𝓜) < j' e(𝓛)`. In particular `z` and every `E`-linear element of `𝔓^{1−r}(𝓛)` lie in `𝔓^{j'}(𝓜)`.

- If `x ∈ 𝔓^{1−r}` (BK93's non-fundamental case), then `s(b) = z + x ∈ 𝔓^{j'}(𝓜)`, and `exists_improvement_of_le` with `ρ = −j'` gives `T` on `𝓜` with `T.r = −j'`.
- Otherwise `x` has valuation exactly `−r` (BK93's scalar-fundamental case). `exists_valuation_of_normalized` gives `ρ` with `v_𝓜(x) = −ρ` and `ρ e(𝓛) = r e(𝓜)`, so `j' ≥ 1 − ρ`. Then `C = [𝓜_E,ρ,ρ−1,x]` is simple (`exists_scalar_simple`) and `s(b) − x = z ∈ 𝔓^{1−ρ}(𝓜)`, that is, `s(b) ∈ C.coset`. `exists_refinement_of_coset` gives `U` on `𝓜` with `U.r = ρ − 1 < ρ`, `β ∈ U.coset`, and the invariants of `F[S.b, x] = F[S.b]`.

In both cases the normalized depth of the new stratum is strictly smaller than `r/e(𝓛)`.
