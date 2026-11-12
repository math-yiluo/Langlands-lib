# Skeleton of the Noetherian-approximation proof

Module `Langlands.AlgebraicGeometry.QuasiAffineApproximation.Skeleton`, by Worker 5045.
It serves the proof of
`Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFNoetherianSchemeApproximationStatement`.
The module states three interface propositions and shows how they combine. They are proved
in `QuasiAffineApproximation.Presentation` (Part I), `QuasiAffineApproximation.Approximation`
(Part II) and `QuasiAffineApproximation.QuotientSpace` (Part III). The interfaces are internal to
this proof; they are not taken from a literature source.

## Idea

The Library's criterion
`SaturatedAffineOpensRepresentation.exists_AF_representation_of_saturated_affine_opens`
works directly over `Spec R`. It says that a finite surjective `f : U ⟶ Y` with
*saturated affine neighbourhoods* makes `Y` an AF scheme. So the proof needs no transport
between `Spec R` and an absolute base, and no descent of affine morphisms. It is enough to
find an affine morphism `U ⟶ P` to an AF scheme `P` that is constant on pairs of points
with the same image in `Y` (`hasSaturatedAffineNeighborhoods_of_affineHom`). The scheme
`P` comes from the Noetherian case applied to a Noetherian model of `Y`.

## Interfaces

- `PresentationInterface` (Part I). A finite surjective `f : U ⟶ Y` from a quasi-affine
  `U` to a qcqs algebraic space over `Spec R` has the following data: an étale equivalence
  relation `E` with affine `E.U`; a finite surjective cartesian cover `E' ⟶ E` (`φ`, `g`);
  and a flat, locally finitely presented, surjective `q : E'.U ⟶ U` whose kernel pair is
  `(E'.t, E'.s)`. Points of `U` with the same image in `Y` lift to points of `E'.U` with
  the same image under `φ`. Here `E` is the kernel pair of an affine atlas of `Y`, and `E'`
  is its pullback along `f`.
- `ApproximationInterface` (Part II). Such data with an arbitrary quasi-affine quotient `M`
  has a Noetherian model. This is a level `E₁' ⟶ E₁` of the same shape with affine `E₁.U`
  and `E₁.R`, Noetherian quasi-affine quotient `M₁`, compatible maps `E.U ⟶ E₁.U`,
  `E'.U ⟶ E₁'.U`, and an *affine* map `M ⟶ M₁`.
- `QuotientInterface` (Part III). From the Noetherian case: such a Noetherian level gives
  an AF scheme `P`, an affine `M₁ ⟶ P` and a map `E₁.U ⟶ P` agreeing on `E₁'.U`. Here `P`
  represents the quotient space `Y₁ = E₁.U / E₁.R` over `Spec ℤ`, to which the Noetherian
  case applies with the finite surjective cover `M₁ ⟶ Y₁`.

## Proof of `approximation_of_interfaces`

Compose `U ⟶ M₁ ⟶ P` (affine). Two points of `U` with the same image in `Y` lift to `ω`,
`ω'` in `E'.U` with `φ ω = φ ω'`. By the commuting squares, their images in `P` are both
the image of `φ ω` under `E.U ⟶ E₁.U ⟶ P`. So the composite is constant on such pairs,
and the criterion applies.
