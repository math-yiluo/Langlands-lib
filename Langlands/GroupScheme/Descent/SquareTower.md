# Tower coherence of commuting-square comparisons

This internal development proves two coherence identities for actual group
scheme pullbacks, over arbitrary schemes at arbitrary common universe `u`.

`squareTowerComparison` constructs the actual isomorphism by traversing two
commuting squares and collapsing the integral pullback tower. Its equality
`squareTowerComparison_eq` identifies the alternate path through the generic
tower first. At the level of group morphisms, `squareComparison_tower` compares two successive commuting squares with their
composite. Performing the two square comparisons and collapsing the integral
pullback tower equals collapsing the generic pullback tower and performing the
composite square comparison. Its hypotheses state both tower composites and
all three commuting squares explicitly. The proof projects to the original
group and uses pullback extensionality and the projection formulas for each
comparison.

`descentBaseChangeIso_tower` proves the usual tower law for the canonical
semilinear isomorphisms of a group pulled back from an original base. It uses
only the universal property of the actual scheme pullback and the canonical
projection formula. No extension property, point stability or existence of an
effective descent solution is assumed or proved.

Both results are internal consequences of the existing pullback comparisons.
They supply coherence identities for constructing integral descent data by
generic rigidity; this unit constructs no such datum itself.
