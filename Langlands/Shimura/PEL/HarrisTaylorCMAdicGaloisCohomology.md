# The Galois action on the m-power torsion limit of Harris's CM coefficient system

This internal construction forms the inverse limit over the torsion stages of
the cohomology of a geometric CM level with Harris's coefficient system, and
studies its Galois action. Fix a small CM level `U` and an algebraic
representation `ρ` of `D.rationalInvolution.baseChange K` on a
finite-dimensional vector space `W` over a number field `K`. Fix also a
rational finite place `p` and the nonzero natural number `m` of the
published construction. Worker 57's published
`cmHarrisGeometricGaloisCohomologyAction ... degree` is the inverse system,
over the stages `r`, of the cohomology modules `H^degree(X̄_U, B_r)` with
their actions of `Gal(F̄/F)`. Here `X̄_U = X_U ×_{Spec F} Spec F̄`, and `B_r`
is the `r`-th stage of the original stable-lattice coefficient system of
`W`, the lattice reduced modulo the `r`-th power of the scalar ideal `(m)` of
the coefficient ring. This module takes the limit of this system in the
category of Galois actions, the `m`-power torsion limit of the cohomology.
With the inverse limit topology of the discrete stages, the limit is
Hausdorff. The Galois action on it is jointly continuous for the Krull
topology when every stage is smooth, as asserted by Worker 3's Library
statement `HarrisCMGaloisCohomologySmoothStatement`. The limit is unramified
at a finite place where every stage is, and its projections to the stages
intertwine the geometric Frobenius endomorphisms. When the limit is finite
free over the coefficient ring, it has a Frobenius Euler polynomial
`det(1 - Frob_w X)`. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, works with coefficients modulo powers of the coefficient prime `ℓ`
(printed p. 308) and forms from them the lisse `ℓ`-adic sheaf (printed
p. 311). §5 on printed p. 313 considers `λ`-adic representations of
the Galois group, with the local factors (5.6) formed from Frobenius
eigenvalues, and Theorem 5.7 concerns those on the cohomology
`H^{n-1}(S_K(N), W)` of the Shimura variety. This module gives the inverse
limit over the stages of the published cohomology of the actual geometric CM
level with Worker 57's version of these coefficient systems, together with
its Galois action, continuity, unramifiedness transfer and Frobenius Euler
polynomial.

The scalar `m` is arbitrary apart from `m ≠ 0`, as in the published
coefficient construction. No relation between `m` and `p` is assumed, and
`m = 1` is allowed, in which case every stage is zero. The limit is the
`(m)`-adic analogue of integral `λ`-adic cohomology. It is not identified
with the `λ`-adic cohomology of Harris for a coefficient prime; that
specialization, for instance a power of the prime below `λ` as `m`, and its
comparison are not constructed here. The coefficient ring is the integral
ring `HarrisCoefficientIntegers K p`, the full product of the valuation rings
at all places of `K` above `p`; no place `λ` is chosen. The module does not
invert `m` or `p`, does not construct the `JL(π_f)`-isotypic component or the
twist by `V(π)`, and proves no finiteness, freeness, smoothness or
unramifiedness: these are hypotheses. Freeness over the coefficient ring is
assumed for the Euler polynomial; the limit may have torsion in general. No
relation between the Euler polynomial of the limit and the characteristic
polynomials of the stages is stated, and no statement of Harris is
formalized.

## Inputs

The binders `E`, `F`, `A`, `D`, `L`, `C`, the named premises `preservation`
through `htor`, `q`, `U`, `[Module.Finite ℚ A]`, `K`, `W`, `ρ`, `p`, `m`,
`hm`, `existence`, `geometry`, `hRigid` and the two `HasDerivedCategory`
instances (universes `wS` and `wR`) are copied from the published
`Langlands.Cohomology.HarrisCMCohomology.Statement`. Below `...` abbreviates
the arguments `D C ... q U ρ p m hm existence geometry hRigid`. Write
`Galois` for `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, which is
definitionally `Field.absoluteGaloisGroup F`, with its Krull topology, and
`Rcoeff` for `HarrisCoefficientIntegers K p`.

- Worker 57's published `cmHarrisGeometricGaloisCohomologyAction ... degree :
  ℕᵒᵖ ⥤ Action (ModuleCat Rcoeff) Galois`
  (`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`), the
  cohomology of the stages of the coefficient system built from
  `harrisCoefficientScalarIdeal K p m = Ideal.span {(m : Rcoeff)}` and its
  powers (`Langlands.Shimura.Coefficients.HarrisReduction`). Every stage is
  killed by `m^r`; its Markdown records that `m` need not be prime and may
  be `1`.
- Worker 3's published
  `Langlands.Cohomology.HarrisCMCohomology.HarrisCMGaloisCohomologySmoothStatement ...`:
  for every degree and every stage `r`, the representation
  `((Rep.ActionToRep Rcoeff Galois).obj ((cmHarrisGeometricGaloisCohomologyAction ... degree).obj r)).ρ`
  is smooth.
- Worker 61's published `Langlands.Cohomology.ContinuousLimit`:
  `ConeSpace`, `act`, `t2Space_of_isLimit`, `continuous_action`,
  `contRepresentation` and `contAction`.
- From `Langlands.Shimura.LimitGaloisAction`, submitted together with this
  module: `isUnramifiedAlong_limit`, `isUnramifiedAt_limit` and
  `geometricFrobenius_limit_π`.
- From `Langlands.Shimura.FrobeniusPolynomial` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `frobeniusEulerPolynomial`,
  `frobeniusEulerPolynomial_eq_along` and
  `eulerPolynomial_eq_frobeniusEulerPolynomial_of_lift`.
- From the published `Langlands.Shimura.DecompositionGroupAction` and
  `Langlands.GaloisRepresentation`: `IsUnramifiedAlong`, `IsUnramifiedAt`,
  `geometricFrobenius`, `localRestriction`, `LocalGroup` and
  `IsGeometricFrobeniusLift`.

## The limit over the torsion stages

- `cmHarrisAdicCohomology ... degree : Action (ModuleCat Rcoeff) Galois` is
  `limit (cmHarrisGeometricGaloisCohomologyAction ... degree)`.
- `cmHarrisAdicCohomologyπ ... degree r` is the projection `limit.π` to the
  stage `r`, a morphism of Galois actions.
- `CMHarrisAdicSpace ... degree` is `ContinuousLimit.ConeSpace` of the limit
  cone: the same module with the coarsest topology making every projection
  to a discrete stage continuous. An instance records that it is Hausdorff.
- `continuous_cmHarrisAdicAction ... hsmooth degree`: if `hsmooth` proves
  `HarrisCMGaloisCohomologySmoothStatement ...`, the action
  `(σ, x) ↦ σ · x` of `Galois` on `CMHarrisAdicSpace ... degree` is jointly
  continuous.
- `cmHarrisAdicContRepresentation`: the action as a representation by
  continuous linear maps.
- `cmHarrisAdicContAction ... degree hsmooth`: for a topology on `Rcoeff`
  acting continuously on the limit, the limit as an object of
  `ContAction (TopModuleCat Rcoeff) Galois`.

## Decomposition groups and Frobenius

Let `w : Global.FinitePlace F` and let `j` be a closure embedding at `w`.

- `cmHarrisAdicCohomology_isUnramifiedAlong ... degree hu`: if every stage is
  `IsUnramifiedAlong (ModuleCat Rcoeff) w _ j`, so is the limit.
  `cmHarrisAdicCohomology_isUnramifiedAt` is the same for `IsUnramifiedAt`.
- `cmHarrisAdicCohomology_geometricFrobenius_π`: the projection to every
  stage intertwines the geometric Frobenius endomorphisms at `w` along `j`.

Assume moreover that the limit is a finite free `Rcoeff`-module.

- `cmHarrisAdicFrobeniusEulerPolynomial ... w degree : Rcoeff[X]` is
  `FrobeniusPolynomial.frobeniusEulerPolynomial w` of the limit, the reversed
  characteristic polynomial of the geometric Frobenius endomorphism along
  Mathlib's chosen closure embedding.
- `cmHarrisAdicFrobeniusEulerPolynomial_eq_along j`: it is the reversed
  characteristic polynomial of the geometric Frobenius endomorphism along any
  `j`.
- `cmHarrisAdicFrobeniusEulerPolynomial_eq_of_lift hu hg`: if every stage is
  unramified at `w` along `j` and `g` is a geometric Frobenius lift, the
  action of `localRestriction w j g` on the limit has reversed
  characteristic polynomial equal to the Frobenius Euler polynomial.

## Proof outline

The topological statements apply `ContinuousLimit` to the limit cone, which
exists because categories of actions on modules have limits; the
continuity statement uses the smoothness of every stage, given by `hsmooth`
at the degree. Unramifiedness and the Frobenius compatibility are the
results of `LimitGaloisAction`, whose preservation hypothesis is supplied by
Mathlib's instances for the forgetful functor of `Action`. The Euler
polynomial statements are those of `FrobeniusPolynomial` for the limit, the
last one using the unramifiedness of the limit.

## Provenance

This is an internal composition of Worker 57's published Galois action on
the cohomology of the original geometric CM torsion coefficient system with
Worker 61's published inverse-limit topology, and with
`LimitGaloisAction` and `FrobeniusPolynomial`. The smoothness input is Worker
3's published statement `HarrisCMGaloisCohomologySmoothStatement`, used as a
hypothesis. No action, limit or polynomial is supplied as input. The limit is
the `m`-power torsion limit for the scalar `m` of the published coefficient
construction; it is not identified with Harris's `λ`-adic cohomology. Harris
(1999), printed pp. 308 and 311, and §5, Theorem 5.7 and formula (5.6) on
printed p. 313, are motivation only.
