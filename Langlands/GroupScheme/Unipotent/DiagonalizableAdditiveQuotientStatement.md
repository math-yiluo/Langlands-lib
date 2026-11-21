# Equivariant smooth additive quotients of smooth connected unipotent groups

Worker 386. This is an internal derived statement. It is a step in the proof of the
conjugacy of sections of trigonalizable groups (Task 7806; Milne, *Algebraic Groups*,
2017, Theorem 16.27, as corrected by `TrigonalizableSectionConjugacySmoothStatement`).
That proof uses it in `Unipotent.DiagonalizableUnipotentCocycle` to run an induction on
the dimension of the unipotent group.

## Statement

`DiagonalizableUnipotentAdditiveQuotientStatement.{u}` says the following. Let `k` be an
algebraically closed field in universe `u` and `Λ` any abelian group in universe `u`. Let
`D = D(Λ)` be the diagonalizable group scheme `Diagonalizable.groupScheme (CommRingCat.of k) Λ`.
Let `U` be a group scheme over `Spec k` that is

- locally of finite type and affine over `Spec k` (`LocallyOfFiniteType U.X.hom`,
  `IsAffineHom U.X.hom`),
- smooth over `Spec k` (`Smooth U.X.hom`),
- connected (`ConnectedSpace U.X.left`),
- unipotent (`IsUnipotent U`),
- nontrivial: `SubgroupFunctor.range (𝟙 U) ≠ ⊥`, that is, some point of `U` on some
  test scheme is not the identity.

Let `a` be any automorphic action of `D` on `U` (an action by group automorphisms on every
test scheme). Then there are a character `χ` in `characterLattice D` and a homomorphism of
group schemes `f : U ⟶ 𝔾ₐ`, where `𝔾ₐ = VectorGroup.groupScheme (CommRingCat.of k) 1`, such that

- the underlying morphism of schemes of `f` is smooth and surjective;
- `f` is equivariant when `D` acts on `𝔾ₐ` through `χ`: for every test scheme `T`, every
  `d : T ⟶ D` and every `x : T ⟶ U`, `f (a.act d x) = (VectorGroup.weightAction χ).act d (f x)`.
  The action `VectorGroup.weightAction χ` multiplies the coordinate of `𝔾ₐ` by the value of
  `χ` at `d`.

The acting group `D` need not be smooth or connected; for example `D = μ_p` in
characteristic `p` is allowed. Its action on `U` need not be linear in any coordinates.

## Why it is true

The proof has three steps.

1. A smooth surjective homomorphism `g : U ⟶ 𝔾ₐ` exists. Over a perfect field, a smooth
   connected unipotent group has a composition series whose successive quotients are
   isomorphic to `𝔾ₐ` (SGA 3, Exp. XVII, Corollaire 4.1.3). The quotient of `U` by the
   last proper term of such a series is `𝔾ₐ`, and the quotient map is smooth and
   surjective, so its differential at the identity is nonzero.
2. Weight decomposition. The morphism `D × U → 𝔾ₐ`, `(d, x) ↦ g (d · x)`, is a regular
   function on `D × U`, so it is a finite sum `Σ_χ χ(d) g_χ(x)` with `g_χ` regular on `U`,
   because the characters form a basis of the coordinate ring of `D`. Comparing
   coefficients of characters in `g (d · (x x')) = g (d · x) + g (d · x')` and in
   `g ((d d') · x) = g (d · (d' · x))` shows that each `g_χ` is a homomorphism
   `U ⟶ 𝔾ₐ` with `g_χ (d · x) = χ(d) g_χ(x)`. Setting `d = 1` gives `g = Σ_χ g_χ`, so some
   `g_χ` has nonzero differential at the identity.
3. A homomorphism `f : U ⟶ 𝔾ₐ` with nonzero differential is smooth (its differential is
   surjective onto the one-dimensional Lie algebra of `𝔾ₐ`; compare the Library's
   `Lie.smooth_of_surjective_differential` in `Lie/SurjectiveDifferentialLifting.lean`). Its image is
   then open, and closed since it is a closed subgroup, so `f` is surjective because
   `𝔾ₐ` is connected.

This module records only the statement. The proof is in
`Unipotent.DiagonalizableAdditiveQuotientProof`, which follows these three steps.

## Example

Let `D = μ_p` act on `U = 𝔾ₐ` in characteristic `p` by `t · x = t x + λ (t − 1) x^p` with
`λ ≠ 0`. This action is not through a character, but `f(x) = x + λ x^p` is a smooth
surjective homomorphism with `f(t · x) = t f(x)`, as the statement predicts.

## Provenance

Internal. The statement is formulated for this proof route; it does not appear in this
form in Milne's book or in SGA 3. Step 1 uses SGA 3, Exp. XVII, Corollaire 4.1.3
(Lemme 4.1.5 identifies forms of `(𝔾ₐ)^r` over a perfect field with `(𝔾ₐ)^r`).
SGA 3 instead handles the non-smooth acting group `μ_p` in Exp. XVII 5.7 with
p-Lie algebras; this statement replaces that argument.
