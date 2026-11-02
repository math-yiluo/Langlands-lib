# Lie algebras of dynamic subgroups

This file states `DynamicLieStatement`, the computation of the Lie algebras of
the dynamic subgroup functors of [Dynamic.Basic](Basic.md) as sums of weight
spaces. It contains no proof.

## The statement

`DynamicLieStatement` quantifies over every field `k : Type u`, every group
scheme `G : GroupScheme (Spec (CommRingCat.of k))` whose structure morphism is
`IsAffineHom` and `LocallyOfFiniteType`, every cocharacter
`χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G` and every element
`X : lieKernel G k`. Here `lieKernel G k` is the kernel of reduction
`G(k[ε]) → G(k)` on actual dual-number points
([Lie.DualNumberKernel](../Lie/DualNumberKernel.md)), so `X.val` is a
`k[ε]`-point of `G` and can be tested for membership in a subgroup functor.

The weight spaces are those of [Torus.Weights](../Torus/Weights.md) for the
commutative group scheme `𝔾_m` acting on `Lie(G)(k)` through `χ` and the
adjoint action: `weightSpace χ ψ` consists of the `X` with
`Ad(χ(t)) X_A = ψ(t) • X_A` for every `k`-algebra `A` and every `t ∈ 𝔾_m(A)`.
The character `Gm.powerHom _ n` is `t ↦ t ^ n`. The statement is the
conjunction of three equivalences, read in `Additive (lieKernel G k)`:

* `X.val ∈ (Dynamic.centralizer χ).carrier _` if and only if `X` lies in the
  weight space of the trivial character `Gm.powerHom _ 0`;
* `X.val ∈ (Dynamic.parabolic χ).carrier _` if and only if `X` lies in the
  supremum, over `n : ℕ`, of the weight spaces of `Gm.powerHom _ n`;
* `X.val ∈ (Dynamic.unipotent χ).carrier _` if and only if `X` lies in the
  supremum, over `n : ℕ`, of the weight spaces of `Gm.powerHom _ (n + 1)`.

The carrier is taken on the test scheme `Spec k[ε]` over `Spec k`, the domain
of `X.val`. No representing subgroup scheme is assumed: the statement compares
the dual-number points of the subgroup functors with the weight spaces.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition,
Proposition 2.1.8(1) (printed p.53): for an affine group `G` of finite
presentation over a ring `k`, with `g_n` the weight-`n` subspace of
`g = Lie(G)` under `t.v = Ad(λ(t)) v`, one has `Lie(Z_G(λ)) = g_0`,
`Lie(U_G(λ)) = g_+ = ⨁_{n>0} g_n` and `Lie(P_G(λ)) = g_0 ⊕ g_+`. Its proof
(Step 1, printed p.54) computes with `k[ε]`-points exactly as stated here.
This formalization restricts to a base field, where an affine group locally
of finite type is of finite presentation. Since `Lie(H) = H(k[ε]) ∩ Lie(G)`
for a subgroup `H` of `G`, CGP's equalities are the three equivalences above;
the direct sums of weight spaces are written as suprema of submodules, which
agree with the direct sums because distinct weight spaces are independent.

Source ID: `conrad-gabber-prasad-2015-pseudo-reductive` (Proposition 2.1.8(1)
and Step 1 of its proof, printed pp.53–54, PDF pp.79–80). This is a
proposition target, with no proof, axiom or instance asserting it.
