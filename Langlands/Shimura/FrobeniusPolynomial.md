# Frobenius polynomials of Galois actions on finite free modules

This internal construction attaches to an action of the absolute Galois
group of a number field `K` on a finite free module over a commutative ring
`R`, and to a finite place `v` of `K`, two polynomials:

- the characteristic polynomial `det(X - Frob_v)` of the geometric Frobenius
  endomorphism at `v`;
- the Euler polynomial `det(1 - Frob_v X)`, its reverse.

Neither depends on the closure embedding used to restrict the action to the
decomposition group at `v`. For an action unramified at `v`, every geometric
Frobenius lift, along every closure embedding, has the same characteristic
polynomial. Both polynomials are unchanged under isomorphism of actions. The
declarations are in namespace `Langlands.Shimura.FrobeniusPolynomial`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 (ii) and formula (5.6) on printed p. 313, describes
Galois representations on isotypic parts of cohomology through the
characteristic polynomials of geometric Frobenius elements at almost all
unramified places. The Euler polynomial here uses the normalization
`det(1 - Frob_v X)` of `Langlands.GaloisRepresentation.eulerPolynomial`.
This module defines these polynomials for actions in
`Action (ModuleCat R) (Field.absoluteGaloisGroup K)`, such as the Galois
actions on the cohomology of the CM tower. The coefficient ring is any
commutative ring and the module only needs to be finite free.

No unramifiedness of any action is proved; the results about unramified
actions take it as a hypothesis. No topology on the Galois group and no
continuity is used. No statement of Harris is formalized.

## Inputs

Let `R` be a commutative ring, `K` a number field, `v : Global.FinitePlace K`
and `M : Action (ModuleCat R) (Field.absoluteGaloisGroup K)`. Closure
embeddings `ι` are elements of
`ClosureEmbedding (NumberField.FinitePlace.embedding v)`, and
`chosenClosureEmbedding` is Mathlib's choice.

The published module `Langlands.Shimura.DecompositionGroupAction` provides
the restriction `localRestriction v ι` from the local group `LocalGroup v`
to `Field.absoluteGaloisGroup K`, the element `localClosureChange v ι κ`
relating two closure embeddings, the predicate `IsUnramifiedAlong` (the
actual inertia subgroup `localInertia v` acts trivially after restriction),
and the Frobenius endomorphism `geometricFrobenius (ModuleCat R) v M ι`: the
action of the chosen geometric Frobenius lift `geometricFrobeniusLift v`
after restriction along `ι`. It also proves `geometricFrobenius_conj`,
`geometricFrobenius_eq_of_lift` and `geometricFrobenius_naturality`.
`IsGeometricFrobeniusLift v g` is from
`Langlands.GaloisRepresentation` (`Langlands/Galois/CompatibleFamily.lean`).

## Linear algebra

For finite free `R`-modules `A` and `B`:

- `charpoly_eq_of_comp_eq e h`: if a linear equivalence `e : A ≃ₗ[R] B`
  satisfies `e ∘ f = g ∘ e`, then `f.charpoly = g.charpoly`.
- `isUnit_charpoly_coeff_zero e`: the constant coefficient of the
  characteristic polynomial of a linear automorphism `e` of `A` is a unit,
  since it is `(-1)^rank · det e`.

## The action by linear automorphisms

- `actionEquiv M g : M.V ≃ₗ[R] M.V` is the linear automorphism by which
  `g : Field.absoluteGaloisGroup K` acts, and `actionEquiv_coe` identifies
  its underlying linear map with `(M.ρ g).hom`. These two need no number
  field hypothesis.

## Characteristic and Euler polynomials

Assume moreover that `M.V` is finite and free over `R`.

- `frobeniusCharpoly v M : R[X]` is the characteristic polynomial of the
  linear map underlying `geometricFrobenius (ModuleCat R) v M ι` for
  `ι = chosenClosureEmbedding _`.
- `frobeniusEulerPolynomial v M : R[X]` is
  `(frobeniusCharpoly v M).reverse`.

Independence and lifts:

- `frobeniusCharpoly_eq_along ι`: for every closure embedding `ι`,
  `frobeniusCharpoly v M` is the characteristic polynomial of
  `geometricFrobenius (ModuleCat R) v M ι`.
- `frobeniusEulerPolynomial_eq_along ι`: the same for the reverse.
- `charpoly_eq_frobeniusCharpoly_of_lift hM hg`: if `M` is unramified at `v`
  along `ι` and `g : LocalGroup v` is a geometric Frobenius lift, then
  `M.ρ (localRestriction v ι g)` has characteristic polynomial
  `frobeniusCharpoly v M`.
- `eulerPolynomial_eq_frobeniusEulerPolynomial_of_lift hM hg`: the same for
  the reverse.

Basic properties:

- `frobeniusCharpoly_monic`: the characteristic polynomial is monic.
- `frobeniusCharpoly_natDegree` and `frobeniusEulerPolynomial_natDegree`:
  if `R` is nontrivial, both have degree `Module.finrank R M.V`.
- `isUnit_frobeniusCharpoly_coeff_zero`: the constant coefficient of the
  characteristic polynomial is a unit.
- `frobeniusEulerPolynomial_coeff_zero`: the Euler polynomial has constant
  coefficient `1`.
- `reverse_frobeniusEulerPolynomial`: if `R` is nontrivial, reversing the
  Euler polynomial gives back the characteristic polynomial.
- `frobeniusEulerPolynomial_eq_det ι b`: for every closure embedding `ι` and
  every finite basis `b` of `M.V`, the Euler polynomial is
  `det(1 - X · A)`, where `A` is the matrix of
  `geometricFrobenius (ModuleCat R) v M ι` in the basis `b`, mapped to
  `R[X]` by `C`.

Invariance under isomorphism: for an isomorphism `e : M ≅ N` of actions
with `N.V` finite and free,

- `frobeniusCharpoly_eq_of_iso v e`: `frobeniusCharpoly v M =
  frobeniusCharpoly v N`;
- `frobeniusEulerPolynomial_eq_of_iso v e`: the same for the Euler
  polynomials.

## Proof outline

`charpoly_eq_of_comp_eq` shows that `e.conj f = g` and applies
`LinearEquiv.charpoly_conj`. `isUnit_charpoly_coeff_zero` uses
`LinearMap.det_eq_sign_charpoly_coeff` and `LinearEquiv.isUnit_det'`.
Independence of the closure embedding is `charpoly_eq_of_comp_eq` for the
action of `localClosureChange v ι κ`, using `geometricFrobenius_conj`. The
lift results use `geometricFrobenius_eq_of_lift`. The constant coefficient of
the Euler polynomial is the leading coefficient of the monic characteristic
polynomial. The degree of the Euler polynomial uses that the constant
coefficient of the characteristic polynomial is nonzero, so its trailing
degree is zero. The determinant formula is
`LinearMap.charpoly_toMatrix` followed by `Matrix.reverse_charpoly`.
Invariance under isomorphism is `charpoly_eq_of_comp_eq` for the linear
equivalence underlying `e`, using `geometricFrobenius_naturality`.

## Provenance

This is an internal construction on top of
`Langlands.Shimura.DecompositionGroupAction` and the Galois-group objects
of `Langlands.GaloisRepresentation`. The normalization `det(1 - Frob_v X)`
is that of `Langlands.GaloisRepresentation.eulerPolynomial`. Harris (1999),
Theorem 5.7 (ii) and formula (5.6) on printed p. 313, is motivation only.
