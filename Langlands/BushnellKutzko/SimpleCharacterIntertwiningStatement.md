# Intertwining and normalizer of a simple character (U5)

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993), Theorem (3.3.2), printed p. 105 (PDF p. 117), and Corollary (3.3.17), printed p. 112 (PDF p. 124). The adjoint lattice shorthand comes from (3.1.1), printed p. 89 (PDF p. 101).

`SimpleCharacterIntertwiningStatement` quantifies over a nonarchimedean local field and a finite-dimensional vector space in independent universes, the specified additive character, and any simple `[𝔄,n,0,β]` and defining sequence starting at `β`. For `0≤m≤n−1` and `m<r=−k₀(β,𝔄)`, and every `θ∈C(𝔄,m,β)`, it gives `I_G(θ)=Y B_β^× Y` and `N_G(θ)=Y 𝔎(𝔅_β)`. The normalizer here preserves the character and its domain.

In the nonscalar case, `simpleCharacterIntertwiningFactor` is precisely the units `g` with `g−1∈𝔔_β^{r−m}𝔑_{k₀(β,𝔄)}(β,𝔄)+𝔍^{⌊(r+1)/2⌋}(β,𝔄)`. Lattice multiplication uses the span of products; outer products in the formulas are pointwise products of subsets of `G`. In the scalar case the outer factor is `{1}`, so the formulas give `G` and `𝔎(𝔄)`, respectively. The upper bound `m<r` is automatic there. This is the proposition only.
