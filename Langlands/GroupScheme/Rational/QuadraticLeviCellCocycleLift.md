# Quadratic cocycles in an opposite cell with an arbitrary middle subgroup

The module `Langlands.GroupScheme.Rational.QuadraticLeviCellCocycleLift` extends the
torus-cell results of [`QuadraticTorusCellCocycleLift`](QuadraticTorusCellCocycleLift.md)
and [`QuadraticOppositeTorusCell`](QuadraticOppositeTorusCell.md) from a torus to an arbitrary
subgroup `c : C ⟶ G` in the middle of the cell. It is used for the Levi subgroup of a minimal
parabolic subgroup, where the middle factor is not commutative.

## Declarations

- `Dynamic.leviOppositeCell χ c` is the morphism of schemes
  `U(χ) × (C × U(-χ)) → G`, `(x, y, z) ↦ x · c(y) · z`, written with the Library's
  `tripleCellMultiplication` and the affine representatives `Dynamic.Affine.unipotentHom χ`
  and `Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)`.
- `Dynamic.lift_comp_leviOppositeCell` evaluates this morphism on points.
- `Dynamic.isOpenImmersion_leviOppositeCell`: for a smooth affine group over a field, if `c`
  represents the dynamic centralizer `Z(χ)` on all test schemes, the cell morphism is an open
  immersion. This is `isOpenImmersion_tripleCellMultiplication` applied to `-χ`, using
  `Z(-χ) = Z(χ)`.
- `GaloisCocycle.exists_leviOppositeCell_coordinates`: let `Q/F` be a field extension,
  `t : C ⟶ G` over `F`, `χ` a cocharacter of `G_Q`, and `σ ∈ Aut(Q/F)` with
  `σ(U(χ)) = U(-χ)` (as Galois transport of subgroup functors). If the cell morphism of `χ`
  and `t_Q` is a monomorphism, there are a subgroup `A₀` of the coefficient points
  `G(Q) = (Spec Q ⟶ G)` and bijections of `A₀` with the rational points of `U(χ)` and of
  `U(-χ)` (the second through `σ`) such that the map
  `(u, c, v) ↦ u · t(c) · σ(v)` on `A₀ × C(Q) × A₀` is injective, and the cell morphism is
  this map in these coordinates.
- `GaloisCocycle.exists_leviCocycle_of_leviOppositeCell`: for `Q/F` quadratic Galois with
  generator `σ`, `t` a monomorphism, `σ(U(χ)) = U(-χ)` and the cell an open immersion, if a
  twisted value `ξ.twist f` at `σ` has cell coordinates `(x, middle, y)`, then there is a
  cocycle `δ` of `C` on `Spec Q → Spec F` with `δ.map t` cohomologous to `ξ` and
  `value δ σ` equal to the coefficient point of `middle`.

## Proofs

The coordinates are those of the torus version: `A₀` is the subgroup of coefficient points
corresponding to the rational points of `U(χ)`, and Galois conjugation identifies it with the
rational points of `U(-χ)` (`galoisTransportRationalEquiv`). Injectivity of the product
follows from the monomorphism property of the cell morphism and the injectivity of the three
coordinate maps. The cocycle is then produced by
`GaloisCocycle.exists_torusCocycle_of_oppositeCell`, which already allows an arbitrary
monomorphism in the middle.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`: the cell argument of the
proof of Lemma 6.28 (printed pp. 369–370) in the generalized form indicated on printed p. 383
for Lemma 6.28', with the open cell `U_P × C × U_P⁻` of a parabolic subgroup and its Levi
subgroup in place of the Bruhat cell.
