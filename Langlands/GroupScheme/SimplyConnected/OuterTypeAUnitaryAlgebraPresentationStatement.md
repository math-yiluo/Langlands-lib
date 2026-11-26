# Outer forms of type A are special unitary groups of algebras with involution

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitaryAlgebraPresentationStatement`.

`Langlands.GroupScheme.OuterTypeAUnitaryAlgebraPresentationStatement.{u}` is a
proposition; this module states it and does not prove it.

## The statement

It quantifies over a field `K : Type u`, a group scheme `G` over `Spec K` with
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, actual index data
`d : TitsIndexData G` and `n : ℕ`, and assumes:

- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- type `A_n`: some bijection `e : d.Vertex ≃ Fin n` carries `d.cartan` to Mathlib's
  `CartanMatrix.A n`;
- outer type: some `σ : SeparableClosure K ≃ₐ[K] SeparableClosure K` and some simple
  vertex `a` satisfy `d.star σ a ≠ a`.

These are the hypotheses of the published
`Langlands.GroupScheme.OuterTypeAUnitarySplitPresentationStatement`, without its
splitting hypothesis on `K`. The conclusion is that there exist

- a field `E : Type u` with `Algebra K E`, `Algebra.IsQuadraticExtension K E` and
  `Algebra.IsSeparable K E`;
- a ring `B : Type u` with `Algebra E B`, `Algebra K B`, `IsScalarTower K E B`,
  `FiniteDimensional E B`, `Algebra.IsCentral E B` and `IsSimpleRing B`, of
  dimension `Module.finrank E B = (n + 1) ^ 2`;
- a `K`-linear involution `τ : Quaternionic.FirstKindInvolution K B` with
  `τ (algebraMap E B x) = algebraMap E B (SU3Root.conjugation K E x)` for every
  `x : E`, that is, a unitary involution;
- a presentation `UnitaryAlgebra.Presentation E τ G`: group isomorphisms from the
  points of `G` with coefficients in every commutative `K`-algebra `R` to the special
  unitary points `SU(B, τ)(R)`, natural in `R`.

The statement does not say that `E` is the field cut out by the star action.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998), §26.A,
Theorem (26.9), printed p. 366 (PDF p. 389), over an arbitrary field `F`: the
functor `(B, τ) ↦ SU(B, τ)` from central simple algebras of degree `n + 1` with a
unitary involution over an étale quadratic `F`-algebra to simply connected
absolutely simple groups of type `A_n` is an equivalence of categories. Its
essential surjectivity gives, for `G` of type `A_n`, a pair `(B, τ)` with
`G ≅ SU(B, τ)`. When the star action is nontrivial (outer type) the centre of `B`
is not split, so it is a separable quadratic field extension `E` of `K`, and `τ`
acts on it by the nontrivial automorphism. The group `SU(B, τ)` is that of §23.A,
paragraph "Unitary involutions", printed p. 346, whose points are those of
`Langlands.Algebra.CentralSimple.UnitaryPoints`. For `n ≤ 1` the outer-type
hypothesis cannot hold, as the Dynkin diagram has no nontrivial automorphism.
