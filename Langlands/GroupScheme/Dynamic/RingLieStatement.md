# Statement: Lie algebras of dynamic subgroups over a ring

Worker 3483.

`Langlands.GroupScheme.DynamicRingLieStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition: the computation of the Lie algebras of the dynamic subgroup
functors of [`Dynamic.Basic`](Basic.md) as sums of weight spaces, over an arbitrary
commutative base ring. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Dynamic.Basic`](Basic.md) (for `Dynamic.centralizer`,
`Dynamic.parabolic` and `Dynamic.unipotent`) and [`Torus.Weights`](../Torus/Weights.md)
(for `weightSpace` and, through its imports, `lieKernel` and `Gm.powerHom`).

It is the version over a ring of
[`DynamicLieStatement`](LieStatement.md), which states the same three equivalences over a
base field. The changes are the binder `[CommRing R]` in place of `[Field k]` and, following
the source, finite presentation in place of finite type for the structure morphism.

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`;
- every group scheme `G : GroupScheme (Spec (CommRingCat.of R))` whose structure
  morphism `G.X.hom` is `IsAffineHom` and `LocallyOfFinitePresentation` (instance
  arguments);
- every cocharacter `χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G`;
- every element `X : lieKernel G R`.

Here `lieKernel G R` is the kernel of reduction `G(R[ε]) → G(R)` on actual dual-number
points ([`Lie.DualNumberKernel`](../Lie/DualNumberKernel.md)), so `X.val` is an
`R[ε]`-point of `G` and can be tested for membership in a subgroup functor. The weight
spaces are those of [`Torus.Weights`](../Torus/Weights.md) for `𝔾_m` acting on
`Lie(G)` through `χ` and the adjoint action: `weightSpace χ ψ` is the `R`-submodule of
`Additive (lieKernel G R)` of the `X` with `Ad(χ(t)) X_A = ψ(t) • X_A` for every
`R`-algebra `A` and every `t ∈ 𝔾_m(A)`. The character `Gm.powerHom _ n` is `t ↦ t ^ n`.

The proposition is the conjunction of three equivalences:

- `X.val ∈ (Dynamic.centralizer χ).carrier _` if and only if `Additive.ofMul X` lies in
  `weightSpace χ (Gm.powerHom _ 0)`;
- `X.val ∈ (Dynamic.parabolic χ).carrier _` if and only if `Additive.ofMul X` lies in
  `⨆ n : ℕ, weightSpace χ (Gm.powerHom _ n)`;
- `X.val ∈ (Dynamic.unipotent χ).carrier _` if and only if `Additive.ofMul X` lies in
  `⨆ n : ℕ, weightSpace χ (Gm.powerHom _ (n + 1))`.

The carrier is taken on the test scheme `Spec R[ε]` over `Spec R`, the domain of `X.val`.
`Dynamic.centralizer χ`, `Dynamic.parabolic χ` and `Dynamic.unipotent χ` are the subgroup
functors of points `g` fixed by conjugation by `χ`, of points whose orbit map
`t ↦ χ(t) g χ(t)⁻¹` extends over the affine line, and of points for which that extension
has value `1` at `0`; these are CGP's `Z_G(λ)`, `P_G(λ)` and `U_G(λ)`. No representing
subgroup scheme is assumed: the statement compares the dual-number points of the
subgroup functors with the weight spaces. The trivial cocharacter is included. No
smoothness or flatness of `G` is assumed.

## Source

Brian Conrad, Ofer Gabber and Gopal Prasad, *Pseudo-reductive groups*, second edition,
Cambridge University Press, 2015; registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, file
`Conrad-Gabber-Prasad--Pseudo-reductive groups (book, 2nd edition)--2015.pdf`
(SHA-256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`).

- Proposition 2.1.8, printed p.53 (PDF p.79): "Let k be a ring, and G an affine k-group
  scheme of finite presentation. Let λ : GL1 → G be a k-homomorphism, and let GL1 act on
  g = Lie(G) through the derivative of the action t.g = λ(t)gλ(t)⁻¹ on G. Define
  g+ = ⨁_{n>0} gn where gn := {v ∈ g | t.v = tⁿv} for n ∈ Z, and define g− and g0
  similarly. (1) We have Lie(ZG(λ)) = g0, Lie(UG(±λ)) = g±, and
  Lie(PG(λ)) = g0 ⊕ g+ inside g."
- Remark after the proposition, same page: "Note that Proposition 2.1.8 only uses the
  underlying k-modules of the Lie algebras. Also, since GL1 is k-flat, the GL1-action on
  g makes sense, and the existence of the weight space decomposition of g is a
  consequence of Lemma A.8.8."
- Proof, printed pp.53–54 (PDF pp.79–80): "We shall compute using points valued in the
  k-algebra of dual numbers k[ϵ]", and Step 1: "Lie(PG(λ)) = PG(λ)(k[ϵ]) ∩ Lie(G) inside
  G(k[ϵ])".

## Derivation from the source

The three equivalences are CGP Proposition 2.1.8(1) over the ring `R`, for the sign `+`:

- By Step 1 of CGP's proof, `Lie(H) = H(R[ε]) ∩ Lie(G)` inside `G(R[ε])` for each of the
  subgroups `H = Z_G(λ), P_G(λ), U_G(λ)`. So CGP's equalities of submodules of `g` say
  that a Lie vector `X` lies in `Lie(H)` if and only if `X` lies in the corresponding
  weight subspace, which is the form of the three equivalences.
- CGP's `g_n = {v ∈ g | t.v = tⁿv}` is read on all points `t` of `GL1`; this is
  `weightSpace χ (Gm.powerHom _ n)`, which imposes the condition for every `R`-algebra `A`
  and every `t ∈ 𝔾_m(A)`.
- CGP's direct sums `g0 ⊕ g+` and `g+ = ⨁_{n>0} gn` are written as suprema of the
  submodules `g_n` over `n ≥ 0` and over `n > 0`. A supremum of submodules is the image
  of their direct sum, and the two agree because distinct weight spaces are independent:
  at the universal point `t` of `𝔾_m`, over `R[t, t⁻¹]`, a weight-`n` vector `v` has
  `t.v = tⁿv`, so its contribution is concentrated on the coefficient of `tⁿ`.
- CGP's `Lie(UG(−λ)) = g−` is the `+` assertion for the cocharacter `−λ`, whose weight-`n`
  space is the weight-`(−n)` space of `λ`. The Lean statement states the `+` sign only.

Hypotheses. CGP assume that `G` is an affine group scheme of finite presentation over `k`.
The Lean statement assumes that the structure morphism `G → Spec R` is affine
(`IsAffineHom`) and locally of finite presentation (`LocallyOfFinitePresentation`). These
are the same class of group schemes. If `G → Spec R` is affine, then `G` is the affine
scheme `Spec A` with `A = Γ(G)`; it is then quasi-compact and quasi-separated over
`Spec R`, and local finite presentation of `Spec A → Spec R` says that the `R`-algebra `A`
is finitely presented, which is finite presentation of `G` over `R`. Conversely a
finitely presented affine `R`-group has an affine, locally finitely presented structure
morphism. So the Lean hypotheses are CGP's, and the statement is CGP's assertion (1) with
the sign `+`. Over a field, finite presentation and finite type agree, and the statement
then specializes to [`DynamicLieStatement`](LieStatement.md), which assumes
`LocallyOfFiniteType`.

This is a proposition target, with no proof, axiom or instance asserting it.
