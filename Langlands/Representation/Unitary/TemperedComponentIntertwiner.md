# An equivariant map from bounded smoothed maps

Module `Langlands.Representation.Unitary.TemperedComponentIntertwiner` proves
`exists_intertwiner`. Let `σ` and `π_W` be jointly continuous representations of `G` on complex
Banach spaces `V` and `W`, `ψ_k` (`k : κ`) test functions such that `χ_n = ψ_{nIdx n}` is an
approximate identity (`IsApproxIdentity`), `W₀ ⊆ W` a closed `π_W`-invariant subspace, and
`B_k : V →L[ℂ] W` bounded maps with values in `W₀` such that

`B_{nIdx n} (σ(a) (σ(ψ_k) v)) = π_W(χ_n) (π_W(a) (B_k v))`

for every `n`, every word `a` in group elements and test functions (`Word`, `wordOp`), every `k`
and every `v`. If some `B_k` is nonzero, there are a subspace `D ⊆ V` and a linear `J : V → W`
with:

1. `σ(g) D ⊆ D` and `J (σ(g) d) = π_W(g) (J d)` for `d ∈ D`;
2. for every test function `φ`: `σ(φ) D ⊆ D`, `J (σ(φ) d) = π_W(φ) (J d)`, and for every `k`
   there is `C` with `σ(φ) (σ(ψ_k) u) ∈ D` and `‖J (σ(φ) (σ(ψ_k) u))‖ ≤ C ‖u‖`;
3. `J d ≠ 0` for some `d ∈ D`;
4. `J d ∈ W₀` for every `d ∈ D`.

Here `σ(φ)` and `π_W(φ)` are the integrated operators `testOp`.

## Proof

Index the generators by `(a, k, v)`: `δ (a, k, v) = σ(a) σ(ψ_k) v` and `γ (a, k, v) = π_W(a) B_k v`,
and let `Lδ`, `Lγ` be the induced linear maps on finitely supported families
(`Finsupp.linearCombination`); `D` is the range of `Lδ`. If `Lδ f = 0` then, by the hypothesis,
`π_W(χ_n) (Lγ f) = B_{nIdx n} (Lδ f) = 0` for all `n`, and `π_W(χ_n) (Lγ f) → Lγ f`, so `Lγ f = 0`.
Hence `Lγ` factors through `D` (`Submodule.liftQ`, `LinearMap.quotKerEquivRange`), and the
factored map extends linearly to `V` (`LinearMap.exists_extend`): `J (Lδ f) = Lγ f`. Prepending a
letter `g` or `φ` to the words acts on `D` as `σ(g)` or `σ(φ)` and on the values as `π_W(g)` or
`π_W(φ)`, which gives 1 and the first part of 2. The family `σ(φ) σ(ψ_k) u` is the generator
`([φ], k, u)` with value `π_W(φ) B_k u`, which gives the bound. For 3, if `B_k v ≠ 0` then
`J (σ(χ_n) σ(ψ_k) v) = π_W(χ_n) B_k v → B_k v`. For 4, every generator value lies in the closed
invariant subspace `W₀`.

## Provenance

Derived from step 4 of the proof sketch in the Markdown of
`Langlands.Analysis.TemperedIrreducibleComponentStatement` (the definition of `J` on `D_z` and its
well-definedness through an approximate identity), stated for an arbitrary representation and
family of bounded maps.
