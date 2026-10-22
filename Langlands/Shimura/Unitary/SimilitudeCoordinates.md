# Coordinate rings representing similitude functors

Author: Worker 254.

This module builds an explicit finitely presented coordinate ring for the
published similitude group `AlgebraInvolution.similitudes` and proves that
it corepresents the published `AlgebraInvolution.similitudeFunctor`. It adds
no axioms. It is used by
`RepresentabilityProof` to prove `SimilitudeRepresentabilityStatement`.

## Setting

The base is an arbitrary commutative ring `R : Type r`, which need not be
a field. `A : Type u` is an `R`-algebra (a ring, not necessarily
commutative) with an `AlgebraInvolution R A` `σ`. The algebra needs a
finite `R`-basis `b : Module.Basis ι R A` with `[Fintype ι]`, so `A` must be
free of finite rank. The general part lets `ι` live in any universe `v`.
Test algebras `S`, `T` are arbitrary commutative `R`-algebras in arbitrary
universes. Over a field every finite-dimensional algebra has such a basis.

## Coordinates

- `coordinate b x i` is the `i`-th coordinate of `x ∈ S ⊗[R] A` in the
  scalar-extended basis `1 ⊗ b_i` (Mathlib's `Algebra.TensorProduct.basis`).
- `ofCoordinates b c = ∑ i, c i ⊗ b i`.
- `coordinate_ofCoordinates`, `ofCoordinates_coordinate`, `ext_coordinate`
  say these are inverse bijections. `coordinate_zero` gives the coordinates
  of zero.
- `changeCoefficients_ofCoordinates` and `coordinate_changeCoefficients` say
  that the published `changeCoefficients f` along `f : S →ₐ[R] T` applies
  `f` to each coordinate. `changeCoefficients_changeCoefficients`
  composes two coefficient changes.

## Variables, equations and the coordinate ring

`SimilitudeVariable ι` has the variables `unit i` (coordinates x_i of g),
`unitInv i` (coordinates y_i of h, the intended inverse), `multiplier` (c)
and `multiplierInv` (d). It is finite when `ι` is, through the injective
map `code` into `Option (Option (ι ⊕ ι))`.

Over the polynomial ring `P = MvPolynomial (SimilitudeVariable ι) R`,
`genericUnit b` is the element `∑ x_i ⊗ b_i` of `P ⊗[R] A` and
`genericUnitInv b` is `∑ y_i ⊗ b_i`. `similitudeRelations` is the set of

- the coordinates of g h - 1 and h g - 1,
- the coordinates of g σ(g) - c, where σ acts through the published
  `σ.baseChange P` and c through the algebra map,
- the scalar c d - 1.

This is the published equation of `mem_similitudes_iff`: g σ(g) equals the
image of the multiplier. The set is finite (`similitudeRelations_finite`),
so `similitudeIdeal`, its span, is finitely generated
(`similitudeIdeal_fg`). The coordinate ring is
`similitudeCoordinateRing b = P ⧸ similitudeIdeal b`. It has an
`Algebra.FinitePresentation R` instance from Mathlib's
`Algebra.FinitePresentation.quotient`. `similitudeQuotient` is the quotient
map.

`similitudeIdeal_le_ker` says that a polynomial map into `S` kills the
ideal once its values satisfy the four equations.

## The universal similitude

The images of g, h in the coordinate ring are mutually inverse
(`universalUnit_mul_inv`, `universalUnit_inv_mul`), giving the unit
`universalUnit`. The images of c and d give the unit
`universalMultiplier`. `universalSimilitude` is the pair, an element of the
published `(σ.baseChange (similitudeCoordinateRing b)).similitudes`.

## Points and classifying maps

- `similitudePoint b f` is the image of the universal similitude under an
  algebra map `f` from the coordinate ring to `S`. It is computed with the
  published `AlgebraInvolution.map`, using `changeCoefficients f` and `f`.
  This is the expression that defines the published `baseChangeMap` on
  morphisms of `CommAlgCat`.
  Simp lemmas give its unit, inverse unit, multiplier and inverse
  multiplier in coordinates. `similitudePoint_id` says the identity map
  gives `universalSimilitude`.
- `similitudePoint_comp` is naturality: composing with `g : S →ₐ[R] T` maps
  the point by `AlgebraInvolution.map` along `changeCoefficients g` and `g`.
- `similitudeValues b x` assigns to the variables the coordinates of a
  similitude x and of its inverse, its multiplier and the inverse
  multiplier. `similitudeHom b x` is the evaluation map
  `MvPolynomial.aeval` at these values, descended to the quotient
  (`Ideal.Quotient.liftₐ`). `similitudeHom_quotient` and
  `similitudeHom_comp` compute it on polynomials.
- `similitudeHomEquiv b` is the bijection between `R`-algebra maps from
  the coordinate ring to `S` and the similitudes over `S`. Its forward map
  is `similitudePoint` and its inverse `similitudeHom`. The simp lemmas
  `similitudeHom_similitudePoint` and `similitudePoint_similitudeHom` give
  the two inverse identities.
- `similitudeHom_map` is the naturality of `similitudeHom` under changes of
  coefficients. `similitudeHom_universalSimilitude` says the universal
  similitude is classified by the identity.

## Corepresentability

In the functorial part the index type and the algebra share a universe:
`ι : Type u` and `A : Type u`. Test algebras live in `CommAlgCat.{max r u} R`.
`similitudeCoordinateAlgebra b` is the coordinate ring as an object of
that category. `similitudeCorepresentableBy b` makes the composite of
`σ.similitudeFunctor.{r, u, max r u}` with the forgetful functor from
groups to types corepresentable by this object. Its bijection is
`similitudeHomEquiv`, and its compatibility is `similitudePoint_comp`.
`similitudeCoyonedaIso b` is the resulting natural isomorphism, obtained
from Mathlib's `Functor.CorepresentableBy.toIso`:

`coyoneda.obj (op (similitudeCoordinateAlgebra b)) ≅ σ.similitudeFunctor ⋙ forget GrpCat`.

For `R = ℚ` this gives the universe `max 0 u = u` of the published target.

## Provenance

This is an internal derived construction. It is the standard elementary
argument that the solution set of finitely many polynomial equations in
coordinates is represented by the quotient of a polynomial ring. No new
claim about the original literature is made here. The target and its
provenance (Kottwitz 1992, Section 1, and Harris 1999, Section 1) are
recorded in the unchanged
[statement documentation](RepresentabilityStatement.md). The module
imports the published `Langlands.Shimura.Unitary.Similitude` and the
Mathlib modules `RingTheory.FinitePresentation`,
`RingTheory.TensorProduct.Free` and `CategoryTheory.Yoneda`, at Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.

The module proves no smoothness, reductivity or group-scheme structure on
the spectrum of the coordinate ring. It also builds no comparison with any
other coordinate choice.
