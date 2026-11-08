# The Akizuki–Witt factor-extension cocycle and inflation

Author: Worker 1839, for task `37d6d58f-e378-4630-8a8c-0f3d7212a970`. This module
formalizes Artin–Tate, *Class Field Theory* (2009), Chapter XIII §3: the cocycle
formula of Theorem 5 for the Akizuki–Witt map and its inflation law, Theorem 6
(`inf v α = (H:1) α`). It is stated for the pushout extensions of
`Langlands.GroupTheory.ExtensionPushout` (Worker 1556). It also records Mathlib's
transfer computed with an arbitrary section.

There is no arithmetic content. The module is the group-cohomological input for
the inflation relation `inf α_{E/F} = [L:E] α_{L/F}` of Weil classes in Tate,
*Number theoretic background* (1979), (1.2.4), printed p.5.

## Cocycle operations

These declarations are in `Langlands.NormalizedTwoCocycle`.

- `npow c n` is the pointwise power of a normalized cocycle.
  `cohomologyClass_npow` proves `cohomologyClass (c.npow n) = n • cohomologyClass c`
  in Mathlib's `H²`. The proof shows that the additive cocycle of the power is
  `n` times the additive cocycle of `c`, and then uses linearity of `H2π`.
- `inflate π ι hι c` is the inflation of a normalized `Q`-cocycle `c` with values
  in `B` to a `G`-cocycle with values in `A`. It is given by
  `(g, h) ↦ ι (c (π g, π h))`, where `π : G →* Q` and `ι : B →* A` satisfies
  `ι (π g • b) = g • ι b`. The cocycle identity is the image under `ι` of that of
  `c`.
- `cohomologyClass_inflate_congr`: cocycles with equal classes have inflations
  with equal classes. The cochain relating the inflations is `g ↦ ι (b (π g))`,
  where `b` is a cochain relating the original cocycles, obtained from the
  published `exists_cochain_of_cohomologyClass_eq`.

## The Theorem 6 identity

The remaining declarations are in `Langlands.GroupExtensionPushout`. Let `H` be a
finite normal subgroup of `G`. Let `rep : G → G` satisfy `σ⁻¹ rep σ ∈ H` for all
`σ`.

- `conj_mul_mem`, `conj_mul_inv_mem` and `conjMulEquiv` give the bijection
  `h ↦ x⁻¹ h y` of `H` when `x⁻¹ y ∈ H`. `prod_mul_right_eq_prod_mul_left`
  reindexes `∏_h F(h y) = ∏_h F(x h)`. `prod_mul_right_mem` is the case `x = 1`,
  which reindexes by right multiplication by an element of `H`.
- `akizukiWittCochain H a rep σ = (∏_h a(h, rep σ)) / ∏_h a(σ, h)`.
- `akizukiWitt_identity` proves, for a normalized cocycle `a` on `G` and all
  `σ, τ`, with `γ = rep σ · rep τ · rep(στ)⁻¹`,

  `(∏_h h • (a(rep σ, rep τ) a(γ, rep(στ))⁻¹) a(h, γ)) · b(στ) = b(σ) · (σ • b(τ)) · a(σ, τ)^{|H|}`,

  where `b = akizukiWittCochain H a rep`. The left product is the inflated
  Akizuki–Witt cocycle of Theorem 5. The proof follows Artin–Tate's proof of
  Theorem 6. Two cocycle identities, at `(h, rep σ, rep τ)` and `(h, γ, rep(στ))`,
  rewrite each factor as `a(h, rep σ) a(h rep σ, rep τ) a(hγ, rep(στ))⁻¹`. The
  products are reindexed by `h ↦ hγ` and by `h rep σ = σ h'`. The cocycle
  identities at `(σ, h, rep τ)` and `(σ, τ, h)` then follow, with a final
  reindexing `h rep τ = τ h'`. The remaining abelian-group identity is checked in
  `Additive A` with `abel`.

## The factor extension

The setting is a surjection `q : W →* G` with a normalized section `t`, an
equivariant kernel map `r : ker q →* A` (the premise of `Section.cocycle`), and a
surjection `π : G →* Q` with finite kernel.

- `Section.lift π t σ` is the normalized section `ρ ↦ t (σ ρ)` of `π ∘ q`,
  built from a normalized section `σ` of `π`.
- `transferKernel π t x h` is the element `t(h) x t(h q(x))⁻¹` of `ker q`, for
  `x` in `ker (π ∘ q)` and `h` in `ker π`. These are the factors of the
  coset-product transfer from `ker (π ∘ q)` to `ker q`.
- `transferKernel_factorKernel` is the computation before Theorem 5. For the
  factor set `x = t(σρ) t(σρ') t(σ(ρρ'))⁻¹` of the lifted section, with
  `γ = σρ σρ' σ(ρρ')⁻¹ = q(x)`, the element `t(h) x t(hγ)⁻¹` is the conjugate by
  `t(h)` of `k(σρ, σρ') k(γ, σ(ρρ'))⁻¹`, multiplied by `k(h, γ)`. Here `k` is the
  kernel factor set of `t`. It is a direct group computation, using
  `γ · σ(ρρ') = σρ σρ'`.
- `kernelMap_transferKernel_factorKernel` applies `r` to that computation, using
  the equivariance of `r`. This gives Theorem 5's formula
  `h • (a(σρ, σρ') a(γ, σ(ρρ'))⁻¹) a(h, γ)` with `a = t.cocycle r hr`.

`cohomologyClass_inflate_pushout` is the main theorem. Suppose `r'` is an
equivariant kernel map of `π ∘ q` with values in a `Q`-module `B`, and `ι : B →* A`
is equivariant along `π`, with

`ι (r' x) = ∏_{h ∈ ker π} r (transferKernel π t x h)`.

Then for every normalized section `s` of `π ∘ q`

`cohomologyClass (inflate π ι hι (s.cocycle r' hr')) = |ker π| • cohomologyClass (t.cocycle r hr)`.

The proof replaces `s` by `Section.lift π t σ`, where `σ = Section.ofSurjective hπ`.
This uses Worker 1556's section independence `Section.cohomologyClass_eq` and
`cohomologyClass_inflate_congr`. It writes `|ker π| •` as the class of `npow`.
`cohomologyClass_eq_of_cochain` with the cochain `akizukiWittCochain` reduces the
goal to `akizukiWitt_identity` for `rep x = σ (π x)`, after the kernel values are
expanded by `kernelMap_transferKernel_factorKernel`.

In the intended application, `W` is a local Weil group, `ker q = W_L` and
`ker (π ∘ q) = W_E`. The hypothesis on `r'` is then the transfer–inclusion
compatibility of reciprocity for `E ⊂ L`.

## Transfer with a section

`transfer_eq_prod_section` holds for a group `N`, a finite-index subgroup `K`, a
homomorphism `ϕ : K →* M` to a commutative group, and `p : N →* P` with finite `P`
and `ker p = K`. For a section `tp` of `p`, it computes Mathlib's
`MonoidHom.transfer`:

`ϕ.transfer x = ∏_{h ∈ P} ϕ (tp(h) x tp(h p(x))⁻¹)`.

The proof applies `MonoidHom.transfer_def` with the left transversal
`c ↦ tp((p c.out)⁻¹)⁻¹`. This is a transversal by `Subgroup.isComplement_range_left`.
It evaluates `x • T` with `Subgroup.smul_apply_eq_smul_apply_inv_smul`, and
reindexes the product over `N ⧸ K` by `c ↦ (p c.out)⁻¹`. This lemma turns
transfer statements into the hypothesis of `cohomologyClass_inflate_pushout`.

## Provenance

Derived formalization of Artin–Tate, *Class Field Theory* (2009), source
`artin-tate-2009-class-field-theory`, Chapter XIII §3 (Akizuki–Witt map): the
transfer computation preceding Theorem 5, Theorem 5 and Theorem 6, printed
pp.135–137 (PDF pp.144–146). Artin–Tate define `v` on cohomology classes. Here the
statement is the combined consequence `inf (V_* β) = (H:1) α`, for the pushout
cocycles of `ExtensionPushout`, with an explicit inflation and coefficient map.
The cochains `c_σ = ∏_h a(h, σ̄)` and `c'_σ = ∏_h a(σ, h)` of Artin–Tate's proof
appear as the quotient `akizukiWittCochain`.
