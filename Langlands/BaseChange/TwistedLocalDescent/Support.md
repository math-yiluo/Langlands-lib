# Compactness and the support of the twisted constant term

Module `Langlands.BaseChange.TwistedLocalDescent.Support`.

`exists_nhds_forall_proj_mem`: let `G` be a locally compact Hausdorff topological group, `θ` a
continuous map of `G`, `K ⊆ G` compact, `P` a closed subgroup, `pr : P → M` continuous, `V ⊆ M`
open and `δ ∈ G`. Suppose that for every `k ∈ K` with `k δ θ(k)⁻¹ ∈ P`, `pr(k δ θ(k)⁻¹) ∈ V`. Then
there is an open `U₀ ∋ δ` such that for all `k ∈ K` and `p ∈ P` with `k⁻¹ p θ(k) ∈ U₀`,
`pr(p) ∈ V`.

Proof: take a compact neighbourhood `U₁` of `δ` and the closed set `Z = pr⁻¹(V^c) ⊆ P ⊆ G`. The set
`T = {(k, y) ∈ K × U₁ : k y θ(k)⁻¹ ∈ Z}` is compact, hence so is its projection to the second
factor; the hypothesis says `δ` is not in it. Then `U₀ = int(U₁)` minus this projection works.

In the local descent it is applied with `K = GL_n(𝒪_E)`, `P` the standard parabolic, `pr` the Levi
projection and `V` the union of the twisted saturations of the windows, the hypothesis being the
classification `exists_levi_twistedConj_of_parabolic`.
