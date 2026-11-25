# A finite-stage form with prescribed Frobenius star action

This internal construction starts with a split pinning `p` of an affine
group `G₀` over a finite field `k : Type u` and a finite-order based
automorphism `θ`. It produces an affine group `G` locally of finite
type over `k`, a finite Galois extension `K/k` in universe `u`, Galois
pinning data `d` of `G` over `K`, and a base-preserving root-datum
equivalence `f` satisfying `f ∘ θ = μ_d(Frob_K) ∘ f`.

First, `baseChangeBasedAut` transports based automorphisms along the
actual lattice equivalence `p.baseChangeRootDatumEquiv`. The unchanged
simple-root support under scalar extension proves that the transported
automorphisms preserve the base. `baseChangeBasedAut_intertwine`
records the full root-datum compatibility.

For `exists_finiteFrobeniusClass`, `finiteFrobeniusAction` supplies
`K/k` of degree `orderOf θ` and an action on the original based root
datum whose Frobenius value is `θ`. Compose that action with
`baseChangeBasedAut` and apply the effective pinned Galois torus
construction to the actual scalar extension of `p`.
`PinnedGaloisStarAction` computes the descended star action.
Composing its based root equivalence with the scalar-extension
equivalence gives `f`; the intertwining equations and the prescribed
Frobenius value prove the asserted equation.

The provenance is internal: this combines the imported finite-field
cyclic action, actual pinning scalar extension, and effective pinned
descent and star-action calculation. It constructs data over a finite
extension; passage to the separable closure is a separate result.
