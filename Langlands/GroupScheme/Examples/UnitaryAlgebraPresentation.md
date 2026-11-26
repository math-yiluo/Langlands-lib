# Presentations of group schemes as special unitary groups of algebras with involution

Module: `Langlands.GroupScheme.Examples.UnitaryAlgebraPresentation`.

Let `F`, `E` and `B` be as in `Langlands.Algebra.CentralSimple.UnitaryPoints`:
fields `F` and `E` with `Algebra F E`, a finite-dimensional central simple
`E`-algebra `B` that is an `F`-algebra through `E`, and an `F`-linear involution
`τ : Quaternionic.FirstKindInvolution F B`. Let `G` be a group scheme over
`Spec F`.

`Langlands.GroupScheme.UnitaryAlgebra.Presentation E τ G` is a structure with two
fields:

- `pointsEquiv R : G.affinePoints R ≃* specialUnitaryPoints E τ R` for every
  commutative `F`-algebra `R : CommAlgCat (CommRingCat.of F)`: a group
  isomorphism from the points of `G` with coefficients in `R` to the special unitary
  points of `(B, τ)` with coefficients in `R`;
- `naturality`: for every morphism `f : R ⟶ S` of commutative `F`-algebras and every
  point `x`, `pointsEquiv S (G.affinePointMap f x)` is
  `specialUnitaryMap E τ f.hom (pointsEquiv R x)`, the image under `f ⊗ id_B`.

So a presentation is a natural isomorphism between the functor of points of `G`
on commutative `F`-algebras and the functor `R ↦ SU(B, τ)(R)`. For an affine group
scheme `G` this is the same as an isomorphism of group schemes `G ≅ SU(B, τ)`. The
structure records data; whether a presentation exists is a separate question.

## Source

`SU(B, τ)` is the special unitary group of Knus, Merkurjev, Rost and Tignol,
*The Book of Involutions* (1998), §23.A, paragraph "Unitary involutions" (printed p. 346, PDF p. 369), with
the points described in `Langlands.Algebra.CentralSimple.UnitaryPoints`. The
structure is the counterpart, for an arbitrary central simple algebra with
involution, of the published `HermitianMatrix.SchemeModel.Presentation`, which
records presentations by special unitary groups of Hermitian matrices; here the
tests are affine, given by commutative `F`-algebras.
