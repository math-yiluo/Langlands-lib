# Rational induction compatibility from two representation identities

Worker 181. This internal assembly retains the two independent universes
`u,v` and has conclusion exactly the unchanged, unapplied published
`RationalInductionCompatibilityStatement.{u,v}`.

`RationalInductionAssemblyPremises.{u,v}` is a Prop-valued conjunction of the
published `RationalGeometricK0ExpansionStatement.{u,v}` and
`RationalInducedK0WeylConjugacyStatement.{u,v}`. Both are hypotheses of
`rationalInductionCompatibility_of_expansion_and_inducedWeyl`; this module
does not prove either representation identity or the unconditional final target.

The implemented proof first introduces every parameter of the published
induction target, with the canonical point topology. The existing
`rationalWeylComparison` gives both exact normalizer and full-centralizer
comparisons. `rootSpanPointCoxeterData` constructs a finite actual point
Coxeter system from the target's relative-root-system witness, maximal
split torus and generic cocharacter. Its root-sign length law supplies the
positive simple-reflection comparison for that same system by
`positiveSimpleReflectionComparison_of_rootLength`; the data also include
the exact actual standard-Levi Weyl identification.

Worker 1186's `pointSourceIntersectionIdentities` now derives all three
structural source identities from the target's standard-cocharacter and
Levi-intersection statements and the proved root comparisons. The imported
point-source adapters derive the actual geometric decompositions and their
finite-length and short-exactness properties. Ambient and restricted-Levi
`ParabolicFiniteLength` are derived from precisely the target's finite-length
preservation, closedness, projection continuity and compact-limit hypotheses.
No subgroup identity or preservation equation is added as a premise.

The expansion hypothesis is applied to these actual geometric terms and
their derived witnesses. A section of the actual normalizer quotient is
chosen using quotient surjectivity. For every minimum representative, the
induced Weyl hypothesis is applied to the two literal fine standard Levis,
whose inverse-conjugation membership equivalence is derived from the source
identities. `pointSourceInducedGeometricTermK0_eq` combines this equality
with actual induction in stages and identifies each induced geometric term
with its literal source induced Levi alternating term.

Finally `inductionCompatibility_of_geometricExpansion` applies the proved
finite signed-intersection identity and sums those terms. Unfolding the
rational ambient and Levi operators identifies its conclusion with the
published target. The sign is exactly `(-1)^|I|`; there is no extra rank sign.
The literal `rootSet`, `leviIndex`, restricted subgroups, every finite
standard-Levi index and carrier universe `max (u+1) v` are preserved.

This is an internal composition of existing constructions and proved
adapters. The source geometry is Worker 1186's work, adapting Worker 1493's
orbit and shift arguments and Worker 181's root-support proof; the actual
Levi identification and common geometric adapters include Worker 165's
contributions, and the induction stages include Worker 438's work.
The geometric expansion and induced Weyl equation remain separate
representation-theoretic proof and publication obligations. No imported
target or its paired Markdown is changed.
