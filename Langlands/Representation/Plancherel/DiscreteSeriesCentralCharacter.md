# Actual unitary central characters of discrete-series classes

Worker 200. This internal construction makes the existing scalar central
character available as an actual function on the canonical discrete-series
classes. It supplies a representation-side input for central Fourier inversion.
It imports the existing `DiscreteSeriesClass`, descended
`SmoothDualClass.HasCentralCharacter`, scalar twists and central-character
regularity. It introduces no new notion of a representation or discrete series.

## Hypotheses and the source of existence

The group and representation-carrier universes are independent. For the class
construction, `G` is a topological group and `A` is a supplied normal central
subgroup. The quotient `G / A` has a measurable structure and a specified Haar
measure `μ`. An element of `DiscreteSeriesClass A hA μ` is an actual canonical
irreducible admissible smooth class satisfying the existing
`IsSquareIntegrableModCentralSubgroup` predicate. That predicate already
contains a full-center `UnitaryCentralCharacter` with its scalar action, open
kernel and norm-one values, as well as the coefficient-integrability assertion.
This construction extracts that existing character datum; it does not deduce
central-character existence from an integral without that datum and does not
assume a new character or desired twist law.

The quotient subgroup `A` remains distinct from the full center. It may later
be specialized to the source's actual split central subgroup. No local-field,
characteristic, splitness, finite central quotient, Borel-space, countability,
carrier norm or carrier topology hypothesis is imposed by this construction.
The unitary unramified action and orbit-map statements additionally use the
existing nonarchimedean group and a family of positive norm characters, with
an independent character-index universe.

## Choice independence and the actual scalar action

The private uniqueness lemma works on the existing smooth dual. After choosing
an actual representative in quotient induction, irreducibility gives a nonzero
vector. If two central characters act by scalars, their scalars agree on that
vector. Cancellation shows equality at every central element and hence equality
of the characters. This uses no Schur existence theorem or dimension bound.

The private existence lemma takes the character witness from the existing
square-integrability predicate at each representative. Its scalar action is
exactly the existing descended `HasCentralCharacter` condition.
`discreteSeriesCentralCharacter` chooses the resulting full-center character
with values in complex units. The accompanying theorems prove its scalar action,
open kernel and norm-one property. The theorem
`discreteSeriesCentralCharacter_eq_of_hasCentralCharacter` proves that it equals
any other character with the same scalar action; thus representative and witness
choices cannot change the result. At an actual inducing representative,
`discreteSeriesCentralCharacter_mk` identifies it with every supplied
`UnitaryCentralCharacter` datum of that representation.

`discreteSeriesUnitaryCentralCharacter` includes those identical complex values
in `Circle`. Its coercion formula is definitional. Its actual-action theorem
says that a central element acts on the representative by multiplication by
this very scalar. The open kernel of the units-valued character makes it
locally constant, and the continuous inclusion of complex units and the
circle subtype give the stated continuity.

## Central restriction and the twisting formula

`discreteSeriesCentralRestriction B hB` composes the full-center character with
the actual inclusion of any supplied central subgroup `B`. The result is a
continuous circle-valued group homomorphism. The subgroup `B` need not equal
the subgroup `A` used for the square-integrability quotient.

For the actual same-carrier scalar twist by `χ`, multiplication of its
restriction to the center with the old central character has precisely the
scalar action of the twisted representation. The private twisting lemma proves
that identity on actual representatives. The existing class twisting operation
and character uniqueness give `discreteSeriesCentralCharacter_unitaryTwist` on
the discrete-series classes themselves. No character twist law is postulated.

`unitaryUnramifiedCircleCharacter` retains the values of an actual unitary
unramified character in `Circle`, with the definitional coercion formula and
continuity. Restricting the proved class twist law to `B` gives

```text
centralRestriction(χ • ω)(b) = χ(b) * centralRestriction(ω)(b).
```

The theorem `discreteSeriesCentralRestriction_orbitMap` is this same formula
for the existing actual `discreteSeriesOrbitMap`. Thus choosing the central
character function on an orbit by restriction of this class map supplies the
representation-side twist premise of a Fourier adapter, once its specified
central subgroup and inclusion are identified. The formula holds at every
actual character and every central subgroup element, with no finiteness or
continuity premise about the entire smooth dual.

## Remaining scope

This is an internal extraction, uniqueness and transport argument from the
published class and coefficient definitions. It defines no topology on the
whole discrete-series set. It proves no Fourier inversion, finite fiber bound,
central Haar normalization, spectral finiteness or Plancherel formula. Rational
split-center identification and a consumer's analytic Fourier theorem remain
separate obligations; this unit supplies the actual central-character map and
its scalar twisting law for them.
