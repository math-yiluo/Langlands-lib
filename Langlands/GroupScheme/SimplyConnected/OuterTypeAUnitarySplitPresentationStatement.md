# Outer forms of type A are special unitary groups when unitary algebras split

Author: Worker 150.

Module: `Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationStatement`.

`Langlands.GroupScheme.OuterTypeAUnitarySplitPresentationStatement.{u}` is a
prerequisite statement for Task 5973. It is not proved here. Over a field `K`
where every central simple algebra with a unitary involution is split (the
property `Langlands.UnitaryInvolutionSplitting K` of
`Langlands.Algebra.UnitaryInvolutionStatements`), it says that every simply
connected absolutely almost-simple group of outer type `A_n` is the special
unitary group of a nonsingular Hermitian form of rank `n + 1`. The group is
presented on every test scheme by actual matrices.

## The statement

It quantifies over a field `K : Type u` and assumes
`UnitaryInvolutionSplitting K`. It then quantifies over a group scheme `G` over
`Spec K` with `IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`, actual
index data `d : TitsIndexData G`, and `n : ℕ`, and assumes:

- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- type `A_n`: some bijection `e : d.Vertex ≃ Fin n` carries `d.cartan` to
  Mathlib's `CartanMatrix.A n`;
- outer type: some `σ : SeparableClosure K ≃ₐ[K] SeparableClosure K` and some
  simple vertex `a` satisfy `d.star σ a ≠ a`.

These are the hypotheses of the published `LocalOuterTypeAHermitianModelStatement`,
except that `K` is an arbitrary field with the splitting property and not a
nonarchimedean local field. The conclusion is that there exist:

- a field `L : Type u` with `Algebra K L`, `Algebra.IsQuadraticExtension K L`
  and `Algebra.IsSeparable K L`;
- a Hermitian form
  `J : HermitianMatrix.Form (SU3Root.fieldInvolution K L) (Fin (n + 1))`, that is,
  an invertible matrix (`J.gram` lies in the general linear group) that equals
  its conjugate transpose for the nontrivial automorphism of `L/K`;
- an element of `HermitianMatrix.SchemeModel.Presentation K L J G`, which is
  published all-test presentation data. For every test scheme `T` over `Spec K`
  it gives a group isomorphism from the `T`-points of `G` to the determinant-one
  isometries of `J` with coefficients in `L ⊗_K Γ(T, 𝒪_T)`, natural in `T` on
  matrix entries.

The statement does not say that `L` is the field cut out by the star action,
and it says nothing about the Witt index of `J`.

## Provenance (derived)

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*, Theorem (26.9)
(printed p. 366, PDF p. 389), holds over an arbitrary field `F`. It says that the
functor `(B, τ) ↦ SU(B, τ)` is an equivalence between central simple algebras of
degree `n + 1` over an étale quadratic `F`-algebra with a unitary involution and
simply connected absolutely simple groups of type `A_n`. The groups of outer type
(nontrivial `*`-action) correspond to algebras whose centre `L` is a field. Here
`L` is a separable quadratic extension of `F`, and `τ` is a unitary involution
relative to the nontrivial automorphism of `L/F`. Under
`UnitaryInvolutionSplitting K`, `B ≅ M_(n+1)(L)`. By Theorem (4.2)(2) of the same
book (printed p. 43, PDF p. 66), a unitary involution on `End_L(L^(n+1))` is
adjoint to a nonsingular Hermitian form `h`. So `G ≅ SU(h)`, which is what the
presentation records, with `J` the Gram matrix of `h`.

The statement is phrased with the Library's actual Tits-index data and the
published `Presentation` structure. "Outer type" is read as nontriviality of
`d.star`, as in `LocalOuterTypeAHermitianModelStatement`. The splitting
hypothesis is kept separate, so that the general-field descent (Theorem (26.9)
together with Theorem (4.2)) and the arithmetic input over local fields
(`LocalUnitaryDivisionCommutativeStatement` and
`UnitaryDivisionSplittingStatement`) can be proved independently. For `n ≤ 1`
the outer-type hypothesis cannot hold, because the Dynkin diagram has no
nontrivial automorphism.

## Intended use

Over a nonarchimedean local field `K`, `UnitaryInvolutionSplitting K` follows from
`LocalUnitaryDivisionCommutativeStatement` and
`UnitaryDivisionSplittingStatement`. A presentation of `G` together with the local
Hermitian congruence results then gives the published
`LocalOuterTypeAHermitianModelStatement`, which implies the target
`LocalAnisotropicTypeAInnerStatement` by the published reduction
`localAnisotropicTypeAInner_of_hermitianModel`.
