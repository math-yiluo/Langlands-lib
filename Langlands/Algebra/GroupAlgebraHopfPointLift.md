# Lifting Hopf points between group algebras along nilpotent thickenings

This module is an internal helper for the étale-local splitting of groups of
multiplicative type (Conrad, *Reductive group schemes*, Appendix B, B.3.4). It works
with the Hopf points of `Langlands.Algebra.FiniteBialgebraHom`: algebra maps
`f : Q →ₐ[R] C ⊗[R] P` compatible with comultiplication and counit (`IsHopfPoint`).
Geometrically these are homomorphisms of group schemes `Spec P_C → Spec Q_C`.

The result is the algebraic core of the formal étaleness of the scheme of homomorphisms
from a finite diagonalizable group `D(A)` to a split group `D(Λ)`. For a surjection
`π : C → D` with nilpotent kernel, each homomorphism `D(A)_D → D(Λ)_D` lifts uniquely
to a homomorphism `D(A)_C → D(Λ)_C`. This is the classical rigidity of homomorphisms
between groups of multiplicative type. The proof below is derived and does not follow a
specific source text.

## Grouplike points

* `IsGrouplikePoint R g` for `g : C ⊗[R] P`, with `P` an `R`-bialgebra, says that
  `(id_C ⊗ Δ) g = g₁ · g₂` and `(id_C ⊗ ε) g = 1`. Here `g₁` and `g₂` are the images of
  `g` under the two factor inclusions `inclFirst`, `inclSecond : C ⊗ P → C ⊗ (P ⊗ P)`.
  This is the usual notion of a grouplike element of the `C`-bialgebra `C ⊗[R] P`,
  written without base-changing the bialgebra structure.
* `isGrouplikePoint_one`, `IsGrouplikePoint.mul`: `1` is grouplike, and grouplike
  points are closed under multiplication (`C ⊗ P` is commutative).
* `isHopfPoint_iff_forall`: an algebra map `f : R[Λ] →ₐ[R] C ⊗[R] P` out of the group
  algebra of an abelian group `Λ` is a Hopf point exactly when it sends every basis
  element `single γ 1` to a grouplike point. Both conditions of `IsHopfPoint` are
  equalities of algebra maps out of `R[Λ]`, and `AddMonoidAlgebra.algHom_ext` reduces
  them to the generators.

## Grouplike points of `C ⊗[R] R[A]` for finite `A`

For a finite abelian group `A`, the module `C ⊗[R] R[A]` is free over `C` with basis
`1 ⊗ single a 1` (`stdBasis`). `coord g a` is the `a`-th coordinate of `g`. Similarly
`stdBasis₂` is the standard `C`-basis of `C ⊗[R] (R[A] ⊗[R] R[A])` indexed by `A × A`.
The coordinate formulas `sum_coord_tmul`, `stdBasis₂_repr_tmul`, `comul_map_eq`,
`inclFirst_mul_inclSecond`, `counit_map_eq`, `repr_comul_map`,
`repr_inclFirst_mul_inclSecond`, `coord_tmul` and `coord_sum_tmul` compute the two sides
of the grouplike conditions in these bases.

* `isGrouplikePoint_iff`: `g` is grouplike iff its coordinates `(coord g a)_{a ∈ A}`
  form a complete family of orthogonal idempotents in `C`
  (`CompleteOrthogonalIdempotents`). The `(x, y)` coordinate of `(id ⊗ Δ) g` is
  `coord g x` if `x = y` and `0` otherwise. The `(x, y)` coordinate of `g₁ g₂` is
  `coord g x * coord g y`. The counit condition says the coordinates sum to `1`.

## Lifting along a nilpotent thickening

Let `π : C →ₐ[R] D`. The map `C ⊗[R] R[A] → D ⊗[R] R[A]` is
`Algebra.TensorProduct.map π id`.

* `coord_map`: coordinates are computed by applying `π` (from the published
  `basis_repr_map`).
* `IsGrouplikePoint.map`: grouplike points map to grouplike points.
* `IsGrouplikePoint.eq_of_map_eq` (assumes every element of `ker π` is nilpotent): two
  grouplike points with the same image are equal. Coordinatewise, they are idempotents
  whose difference is nilpotent, so they agree (`eq_of_isNilpotent_sub_of_isIdempotentElem`).
* `IsGrouplikePoint.exists_map_eq` (assumes `π` surjective with nilpotent kernel): every
  grouplike point of `D ⊗[R] R[A]` lifts to a grouplike point of `C ⊗[R] R[A]`. Mathlib's
  `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` lifts the coordinate family.
* `bijective_pushPoint` (main result; assumes `π` surjective with nilpotent kernel): for
  every abelian group `Λ`, the published `pushPoint R π` is a bijection from Hopf points
  `R[Λ] → C ⊗[R] R[A]` to Hopf points `R[Λ] → D ⊗[R] R[A]`. Injectivity applies
  `eq_of_map_eq` to each generator. For surjectivity, lift the image of each `single γ 1`
  to a grouplike point `L γ`. Uniqueness of lifts shows that `γ ↦ L γ` is a monoid
  homomorphism `Multiplicative Λ →* C ⊗[R] R[A]`, and `AddMonoidAlgebra.lift` turns it
  into the required Hopf point.

No finiteness or freeness of `Λ` is needed. `A` is finite and carries `DecidableEq`
where coordinates are compared.
