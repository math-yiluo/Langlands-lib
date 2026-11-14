# The λ-adic cohomology of a CM level as a λ-adic Galois representation

This module packages the Library's `λ`-adic cohomology
`H^d(S_U ×_F F̄, W)_λ` of a small CM level `U` with Harris's coefficient
system `W` (`cmHarrisLambdaCohomology`, module
`HarrisTaylorCMLambdaCohomology`) as a `λ`-adic Galois representation of `F`
(`Langlands.GaloisRepresentation.LambdaAdic F K l.1`, that is `Objects F K_λ`).
It does this under the published finiteness and continuity propositions, which
are explicit hypotheses. It also identifies the Euler polynomial at an
unramified finite place through geometric Frobenius. All declarations are in
namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed p. 313, works with `λ`-adic representations `σ` of
`Gal(F̄/F)` unramified at all but finitely many places, with local factor (5.6)
defined through the eigenvalues of `σ(Fr_w)` for a geometric Frobenius `Fr_w`.
The isotypic parts and multiplicity spaces of the cohomology are packaged in
this way in `HarrisTaylorCMLambdaTower`. This module packages the whole
fixed-level cohomology `H^d(S_U ×_F F̄, W)_λ` in the same way, so that
properties of the full cohomology at a level (for example a Hodge–Tate
decomposition at places above `ℓ`) can be stated with the Library's Galois
representation API.

Finite dimensionality and continuity are not proved here. They are the
published propositions `CMHarrisLambdaCohomologyFiniteDimensional` and
`CMHarrisLambdaCohomologyContinuous`, taken as hypotheses. Unramifiedness at a
place is the published proposition `CMHarrisLambdaCohomologyUnramifiedAt`.

## Inputs

The section variables are those of `HarrisTaylorCMLambdaCohomology`: the
central simple unitary data `D`, the charts `C`, the conditional statements
`preservation … htor` and the representability statement `q`, a small level
`U : SmallCMLevel D`, the algebraic representation `ρ` of
`D.rationalInvolution.baseChange K` on a finite-dimensional `K`-vector space
`W`, the place `p` of `ℚ` giving the coefficient prime `ℓ`, the statements
`existence` and `geometry`, the rigidity hypothesis `hRigid` at `U`, the
derived-category instances, a place `l : FinitePlacesAbove K p` (the place
`λ`), and a degree `degree`. In addition:

* `hfin : CMHarrisLambdaCohomologyFiniteDimensional … U ρ p existence geometry
  hRigid l degree`, that `H^d(S_U ×_F F̄, W)_λ` is finite-dimensional over
  `K_λ`;
* `hcont : CMHarrisLambdaCohomologyContinuous … l degree`, that every orbit map
  `g ↦ g · x` of `Gal(F̄/F)` on `H^d(S_U ×_F F̄, W)_λ` is continuous for the
  module topology over `K_λ`.

## Declarations

* `cmHarrisLambdaCohomologyObjects … hRigid l degree hfin hcont :
  LambdaAdic F K l.1` is the continuous finite-dimensional representation of
  `Gal(F̄/F)` over `K_λ` on the space of `cmHarrisLambdaCohomology … l degree`.
  It is the published `continuousOrbitsObjects` applied to this action, with
  `hfin` as the finiteness instance and `hcont` as the continuity hypothesis.
* `cmHarrisLambdaCohomologyObjects_representation_apply`: a Galois element `g`
  acts by `((cmHarrisLambdaCohomology …).ρ g).hom` (`rfl`).
* `cmHarrisLambdaCohomologyObjects_rank`: the rank of the representation is
  `Module.finrank K_λ` of the cohomology (`rfl`).
* `hasEulerPolynomialAt_cmHarrisLambdaCohomologyObjects_iff (v)`: for a finite
  place `v` of `F` and a polynomial `P` over `K_λ`, the representation has
  Euler polynomial `P` at `v` if and only if
  `CMHarrisLambdaCohomologyUnramifiedAt … v` holds and `P` is the Frobenius
  Euler polynomial `FrobeniusPolynomial.frobeniusEulerPolynomial v` of the
  cohomology.
* `hasEulerPolynomialAt_cmHarrisLambdaCohomologyObjects ι hu`: for a closure
  embedding `ι` at `v` and `hu : CMHarrisLambdaCohomologyUnramifiedAt … v`, the
  representation has Euler polynomial at `v` equal to
  `(geometricFrobenius (ModuleCat K_λ) v (cmHarrisLambdaCohomology …) ι).hom.charpoly.reverse`,
  that is `det(1 − X · σ(Fr_v))` for a geometric Frobenius along `ι`.

The two Euler polynomial statements, the Frobenius Euler polynomial and the
geometric Frobenius need the finiteness of the cohomology. Their statements
supply it from `hfin` by `haveI`.

## Proof outline

The definition is `continuousOrbitsObjects`
(`Langlands.Shimura.ContinuousIsotypicGaloisRepresentation`) applied to
`cmHarrisLambdaCohomology`. `CMHarrisLambdaCohomologyFiniteDimensional` is by
definition `FiniteDimensional K_λ` of its space, which is the
`Module.Finite` instance required. `CMHarrisLambdaCohomologyContinuous` is by
definition `HasContinuousOrbits` of the action. The representation and rank
lemmas hold by `rfl`. The Euler polynomial criterion is
`hasEulerPolynomialAt_continuousOrbitsObjects_iff`, since
`CMHarrisLambdaCohomologyUnramifiedAt` is by definition `IsUnramifiedAt` of
the action. The Frobenius statement is
`hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong`, with
unramifiedness transported along `ι` by
`DecompositionGroupAction.isUnramifiedAt_iff_along`.

## Provenance

The construction is internal. It specializes the published packaging of
finite-dimensional Galois actions with continuous orbits to the Library's
`λ`-adic cohomology. The notion is that of Harris (1999), §5, printed p. 313
(PDF p. 15): `λ`-adic representations of `Gal(F̄/F)` unramified at all but
finitely many places, with local factor (5.6) through the eigenvalues of
`σ(Fr_w)` for a geometric Frobenius `Fr_w`. The source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The Euler polynomial is the Library's `HasEulerPolynomialAt`, the reversed
characteristic polynomial of a geometric Frobenius. Its roots are the inverses
of the eigenvalues `β` in (5.6). The normalization of (5.6) by `|β|` is not
formalized.
