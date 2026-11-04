# Actual unipotence and finite coefficient matrices

Authors: Worker 572 (Lean statement and first Markdown draft); Worker 1512
(Markdown revision and submission).

The module defines one proposition,
`Langlands.GroupScheme.UnipotentMatrixCriterion.CorepresentedMatrixUnipotenceStatement.{u}`.
It is a statement only: no proof of the equivalence is given here.

## The statement

Fix an arbitrary universe `u`. The proposition says: for every field
`k : Type u`, every group-valued functor
`F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}` on commutative
`k`-algebras, every commutative `k`-algebra `B : CommAlgCat.{u} (CommRingCat.of k)`
and every corepresentation `e : (F ⋙ forget GrpCat).CorepresentableBy B`,

```text
letI := AffineLinearEmbedding.bialgebra e
IsUnipotent (Corepresented.groupScheme F e) ↔
  CoalgebraUnipotence.IsMatrixUnipotent k B.
```

Corepresentability is part of the given data `e`; the statement does not assert
that an arbitrary functor is corepresentable. There is no finite type,
smoothness, reducedness, connectedness, perfectness or characteristic
hypothesis on `k`, `F` or `B`. Both predicates are the published ones, used
unchanged.

## The bialgebra structure

The right side needs a bialgebra structure on `B`. It is exactly the published
`AffineLinearEmbedding.bialgebra e : Bialgebra (CommRingCat.of k) B`, introduced
by `letI`. It is Mathlib's `Bialgebra.ofAlgHom` applied to the algebra maps
`AffineLinearEmbedding.comul e : B →ₐ B ⊗ B` and
`AffineLinearEmbedding.counit e : B →ₐ k`. The comultiplication classifies the
product of the two points of `F (B ⊗ B)` given by the two tensor inclusions. The
counit classifies the identity of `F k`. The underlying `k`-algebra structure is
that of `B` as an object of `CommAlgCat`, so `v j • a i j` below uses the
algebra scalar action. No other bialgebra structure on `B` is assumed or used.
`CommRingCat.of k` has carrier `k`, so this instance is the
`Bialgebra k B` instance required by `IsMatrixUnipotent`.

## The left side: unipotence of the actual group scheme

`Corepresented.groupScheme F e` is the Library's affine group scheme over
`Spec k` with underlying scheme `Spec B`. Its group law comes from the group
structure of `F` through the corepresentation `e`.

`IsUnipotent G` (from `Langlands.GroupScheme.Reductive.Basic`) means: for every
index type `n : Type` with `Fintype`, `DecidableEq` and `Nonempty` instances, and
every actual homomorphism of group schemes
`ρ : MatrixRepresentation G n`, that is,
`ρ : G ⟶ GeneralLinear.groupScheme n (CommRingCat.of k)`,
there is `v : n → k` with `v ≠ 0` and `ρ.IsFixedVector v`. The index type lives
in `Type`, independently of `u`.

`ρ.IsFixedVector v` is an all-test condition. For every scheme `T` over
`Spec k` and every point `g : T ⟶ G.X` over `Spec k`, the invertible matrix
`ρ.pointMatrix T g` over `Γ(T, 𝒪_T)` fixes the image of `v` in
`Γ(T, 𝒪_T)ⁿ`. The image is taken coordinatewise along the structure map
`scalarMap T : k → Γ(T, 𝒪_T)`. The test schemes `T` range over all schemes over
`Spec k`, including nonaffine ones.

## The right side: positive-size `Fin N` coefficient matrices

`CoalgebraUnipotence.IsMatrixUnipotent k B` (from
`Langlands.GroupScheme.CoalgebraUnipotence.Definitions`) means: for every natural
number `N` with `0 < N` and every matrix `a : Matrix (Fin N) (Fin N) B` satisfying
`CoalgebraUnipotence.IsCoefficientMatrix a`, there is `v : Fin N → k` with
`v ≠ 0` and, in every row `i`,

```text
∑ j, v j • a i j = v i • 1.
```

Here `IsCoefficientMatrix a` means that, for all `i` and `j`,

- `Coalgebra.comul (a i j) = ∑ l, a i l ⊗ₜ a l j`, and
- `Coalgebra.counit (a i j) = (1 : Matrix (Fin N) (Fin N) k) i j`, which is `1`
  if `i = j` and `0` otherwise.

The comultiplication and counit are those of the bialgebra instance above.
Both sides therefore quantify over nonempty finite index sets. The left side
uses an arbitrary finite type `n : Type`, and the right side uses `Fin N` with
`N > 0`.

## Provenance

This is an internal statement. It compares two existing Library definitions and
makes no new assertion taken from the literature. The literature motivation of
the right side, Milne's coefficient form of comodules and his fixed-vector
description of unipotence, is recorded in the paired Markdown of
`CoalgebraUnipotence.Definitions`.

The published adapter `Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates`
supplies the ingredients intended for a proof. This module imports neither it
nor any proof, and proves neither direction.

- From a representation `ρ`, `coefficientMatrix e ρ` is the matrix of `ρ` at the
  universal point `e.homEquiv (𝟙 B)`. `coefficientMatrix_comul` and
  `coefficientMatrix_counit` give its comultiplication and counit identities.
  `isFixedVector_iff` shows that `ρ.IsFixedVector v` holds exactly when
  `∑ j, v j • a i j = v i • 1` for every `i`.
- Conversely, from a coefficient matrix, the published
  `Corepresented.LinearEmbedding.toGL` constructs an actual representation.
  `coefficientMatrix_toGL` recovers the original matrix from it.
- Changing between an arbitrary nonempty finite index type `n` and
  `Fin (Fintype.card n)` relates the two quantifications.

A proof is left to a separate proof task. This module asserts no conilpotence
characterization, quotient theorem or closed-subgroup inheritance theorem.
