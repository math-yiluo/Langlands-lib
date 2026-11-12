# Inflation of factor-extension classes along a norm-compatible kernel map

Author: Worker 5095, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. This module
proves the inflation law `inf α_{E/F} = [L:E] α_{L/F}` for factor-extension
classes when the kernel maps are related by a norm. It is stated for the pushout
extensions of `Langlands.GroupTheory.ExtensionPushout` (Worker 1556) and uses the
cocycle identity `akizukiWitt_identity` of `Langlands.GroupTheory.ExtensionAkizukiWitt`
(Worker 1839).

There is no arithmetic content. In the intended application `W` is the Weil group
of a local field `F`, `ker q = W_L` and `ker (π ∘ q) = W_E` for a tower
`F ⊂ E ⊂ L` with `E/F` and `L/F` Galois. The norm hypothesis is then the
compatibility of reciprocity with the inclusion `W_L ⊂ W_E`, which corresponds to
the norm `Lˣ → Eˣ` (Tate, *Number theoretic background* (1979), (1.2.2), printed
p.4).

## Setting

All declarations are in `Langlands.GroupExtensionPushout`. The data are:

- a surjection `q : W →* G` with a normalized section `t`, and an equivariant
  kernel map `r : ker q →* A` to a `G`-module `A`
  (`r (x n x⁻¹) = q x • r n`, the premise of `Section.cocycle`);
- a homomorphism `π : G →* Q` and a normalized section `σ` of `π`.

## Declarations

- `kernelInclusion π : ker q →* ker (π ∘ q)` is the inclusion of kernels
  (`Subgroup.inclusion`). `kernelInclusion_coe` says it does not change the
  underlying element of `W`.
- `liftDifference π t σ γ` is the element `t(γ) t(σ(π γ))⁻¹` of `ker (π ∘ q)`.
  It compares the section `t` with the lifted section `t ∘ σ ∘ π`. It lies in the
  kernel because `π (q (t γ)) = π γ = π (q (t (σ (π γ))))`.
- `kernelInclusion_factorKernel` decomposes the factor set of `t`, viewed in
  `ker (π ∘ q)`, through the factor set of the lifted section
  `Section.lift π t σ` (Worker 1839). Writing `d = liftDifference π t σ`,
  `s' = t ∘ σ` and `c(x) = s'(π g) x s'(π g)⁻¹`, it states

  `t(g) t(g') t(gg')⁻¹ = d(g) · c(d(g')) · s'(π g) s'(π g') s'(π(gg'))⁻¹ · d(gg')⁻¹`.

  This is a direct group identity, using `π (g g') = π g · π g'`, proved by `group`.

## Main theorem

`cohomologyClass_inflate_norm` assumes that `π` is surjective with finite kernel `H`.
It also assumes a `Q`-module `B`, an equivariant `ι : B →* A`
(`ι (π g • b) = g • ι b`), and a normalized section `s` of `π ∘ q`. Let
`r' : ker (π ∘ q) →* B` be an equivariant kernel map whose restriction to `ker q`
is the `H`-norm of `r`:

`ι (r' x) = ∏_{h ∈ H} h • r x` for all `x ∈ ker q`.

Then

`cohomologyClass (inflate π ι hι (s.cocycle r' hr')) = |H| • cohomologyClass (t.cocycle r hr)`

in Mathlib's `H²(G, A)`.

The proof runs as follows.

1. Put `σ = Section.ofSurjective hπ`. Worker 1556's section independence
   `Section.cohomologyClass_eq` and `cohomologyClass_inflate_congr` replace `s` by
   the lifted section `Section.lift π t σ`. `cohomologyClass_npow` writes
   `|H| •` as the class of the pointwise power `npow`.
2. Let `a = t.cocycle r hr`. Take the cochain `γ ↦ b(γ) / u(γ)`, where
   `b = akizukiWittCochain H a id` and `u(γ) = ι (r' (d γ))`.
   `cohomologyClass_eq_of_cochain` reduces the goal to a pointwise cocycle identity.
3. `akizukiWitt_identity` with representative function `rep = id` is valid since
   `σ⁻¹ σ = 1 ∈ H`. Then `γ = 1`, and the normalization of `a` turns it into
   `(∏_h h • a(g, g')) · b(gg') = b(g) · (g • b(g')) · a(g, g')^{|H|}`.
4. Applying `ι ∘ r'` to `kernelInclusion_factorKernel` gives
   `∏_h h • a(g, g') = u(g) · (g • u(g')) · ι(r'(lifted factor set)) · u(gg')⁻¹`.
   This uses the multiplicativity and equivariance of `r'` and `ι`, and the norm
   hypothesis on the left side.
5. Substituting step 4 into step 3 gives the required identity. It is checked in
   `Additive A` with `abel`.

## Provenance

Derived. The cocycle identity of step 3 is the computation in the proof of
Artin–Tate, *Class Field Theory* (2009), source
`artin-tate-2009-class-field-theory`, Chapter XIII §3, Theorem 6, printed
pp.136–137 (PDF pp.145–146). Here the representative function is the identity
rather than a choice of coset representatives, so it says that the pointwise
`H`-norm of a cocycle on `G` is cohomologous to its `(H:1)`-th power. The
decomposition `kernelInclusion_factorKernel` and the norm-compatible form of the
statement are internal to this project. They are the group-theoretic form of the
inflation relation `inf α_{E/F} = [L:E] α_{L/F}` for Weil classes in Tate,
*Number theoretic background* (1979), source `tate-1979-number-theoretic-background`,
(1.2.4), printed p.5, which also refers to Artin–Tate's Theorem 6.
