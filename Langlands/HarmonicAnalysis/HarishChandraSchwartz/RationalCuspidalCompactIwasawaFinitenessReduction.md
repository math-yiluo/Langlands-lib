# Structural choices for conditional cuspidal finiteness

This is a derived, conditional structural adapter. Its entry proposition,
`RationalCuspidalCompactIwasawaFinitenessReductionStatement`, retains three global premises:

1. `RationalIwasawaCompactExistenceStatement.{u}`;
2. `RationalCuspidalCentralProjectionFiniteStatement.{u}`;
3. `RationalCuspidalFixedCoefficientLiftingStatement.{u, uV}`.

Its conclusion is the unchanged
`RationalFixedCoefficientFinitenessStatement.{u, uV}`. The field universe `u`
and representation-carrier universe `uV` are independent.

The first premise supplies a maximal split torus, a generic cocharacter and a
compact open subgroup with the empty-index standard-parabolic Iwasawa
factorization. The proof obtains these witnesses together by applying that
premise to the actual connected reductive group, under the canonical
`rationalPointTopology`. It then uses precisely those witnesses in the analytic
implication.

This version replaces the stronger `IwasawaExistenceStatement` premise in the
previous published adapter. It no longer asks for a prescribed torus and
chamber, building data, a special vertex or a product family for all parabolics.
The imported `RationalIwasawaCompactExistence` module proves
`rationalIwasawaCompactExistence_of_iwasawaExistence`, so the previous stronger
premise still suffices. It also proves
`rationalIwasawaCompactExistence_of_bruhatTitsAvailability`: Bruhat–Tits
availability implies the minimal structural premise used here. These are
conditional implications; this adapter does not prove structural existence
or availability outright.

The positive-dimensional closed matrix representation is provided by
`Langlands.Plancherel.exists_isClosedSubgroup_fin_succ` in
`Langlands.Representation.Plancherel.ParabolicCharacterDecayProof`.
The split-component inclusion is a closed immersion, so
`isClosedEmbedding_rationalPointMap` makes its rational-point image a closed
subgroup of the locally compact rational-point group. Its subgroup topology is
therefore locally compact. The adapter selects `Measure.haar` on this actual
image, with its induced Borel measurable space.

With those choices,
`RationalCuspidalCentralProjectionFiniteStatement.fixedCoefficientFiniteness`
applies to the arbitrary quotient Haar measure, compact open level and
continuous unitary central character in the exact fixed-coefficient target.
Continuity of the character composed with `Units.val` supplies the
measurability clause of `IsUnitaryCharacter`. The published implication uses
the actual level-preserving lifting premise and the finite projected level
span. The target's additional central-character triviality assumption is not
needed by this stronger conditional implication.

Finally, `rationalDiscreteSeriesOrbitFiniteness_of_compactIwasawaCuspidalInputs` applies
`RationalFixedCoefficientFinitenessStatement.orbitFiniteness` to the preceding
conditional result with the same three premises and independent universes.

The provenance is the composition and structural specialization of the named
published declarations. No new original-source translation is claimed. The
construction adds no analytic argument, reconstruction hypothesis or
rank-induction step. Compact-open Iwasawa existence, finite central projection
and level-preserving lifting remain unproved inputs here; neither
unconditional finiteness target is discharged by this module.

The original full-Iwasawa reduction remains in
`RationalCuspidalFinitenessReduction`. This separately named version preserves
the reviewed weaker-premise statement without changing the original proposition.
