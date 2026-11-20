# Integrality of the Artin conductor of a local Weil representation

`Langlands.Henniart.weilArtinConductorExistence` proves
`Langlands.Henniart.WeilArtinConductorExistenceStatement.{uK, uW}`. For each
irreducible Weil class over a p-adic field, it gives a representative and a
finite inertia presentation with surjective inertia restriction whose
rational Artin conductor is the cast of a natural number.

## Proof

Take a continuous representative of the class. Restrict it to the common
closure's Weil subgroup at the base field and lift its carrier to
`max uK uW` using `universeLiftRepresentation`. This places the representation
in the carrier universe of the virtual group while keeping `uK` and `uW`
independent. The base inclusion identifies the restricted action on the
lifted carrier with the original Weil action via `universeLiftEquiv`.

Write `x` for the lifted representation's virtual class. By
`commonClosureDegreeZeroGeneration` and `exists_finset_generators`, the
class `x - degree(x) · [1]` is in the integral span of a finite set of
induced differences of continuous characters. Take an inertia presentation
of the lifted representation using `continuousWeilFiniteInertiaPresentation`.
Then `exists_presentingField` gives a finite Galois extension `M/K` refining
that presentation and presenting both characters of every chosen generator.

On a generator `Ind_{W_L}^{W_K}([χ] - [χ′])`,
`conductorFunctional_induce_eq` expresses the conductor functional at `M`
as a quotient of group orders times the difference of two rank-one
conductor sums. The Weil subgroup index is the residue degree times the
inertia index, and the inertia index cancels the ratio of inertia orders.
The factor is therefore the residue degree of `L/K`. The published rank-one
comparison `lClassSum_eq_characterConductor`, evaluated with the normalized
reciprocity family from `commonClosureReciprocityExistence`, identifies each
rank-one sum with the natural multiplicative conductor of the corresponding
character. Thus the functional takes integer values on every generator.
It vanishes on `[1]`, so its inverse image of the integer-cast subgroup
contains both the span and `degree(x) · [1]`. It follows that its value at
`x` is an integer.

By `conductorFunctional_baseClass`, this value is the rational Artin
conductor of the refined presentation, viewed in `ℂ`. The rational
conductor is a sum of nonnegative weighted codimensions of fixed spaces,
so the integer is nonnegative and gives a natural witness.
`exists_presentation_of_equiv` carries the refined presentation and its
conductor back to the chosen representative.

## Source comparison

Serre's *Local Fields*, Chapter VI, §2, Theorem 1′ and its proof (printed
pp. 99–102), give nonnegative integral conductors for characters of finite
Galois groups by Brauer induction and rank-one integrality. The weighted
codimensions are in Proposition 2, Corollary 1′. The induction computation
here uses the degree-zero form of Proposition 4, whose discriminant term
cancels on a difference of two rank-one characters. The published rank-one
comparison uses upper numbering and local reciprocity to express the
rank-one Artin sum as a unit-filtration conductor. Lean applies these
ingredients directly to virtual Weil classes and uses a single common finite
inertia presentation to supply the witness for the stated proposition.

Serre's 1979 edition is registered as `serre-1979-local-fields`.
