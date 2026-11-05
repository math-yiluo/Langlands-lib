# Actual root presentations from explicit dynamic structure

Authors: Worker 1294 and Worker 1491.

This internal assembly constructs a root presentation for the actual supplied
parabolic, rational Levi and split-component morphisms. Four structural
statements remain explicit arguments: `GenericMinimalParabolicStatement`,
`RelativeRootNegationStatement`, `ParabolicDynamicStatement`, and
`DynamicGeometricUnipotentRadicalStatement`. This module does not discharge
these statements or prove the unconditional aggregate target.

`parabolicRootPresentationOfDynamicStructure` first uses
`DynamicLeviConjugacy.parabolicLeviRealizingCocharacter` to construct a single
ambient cocharacter realizing the image of the supplied parabolic and the
image of the supplied Levi composite. It obtains both image equalities from
that chosen cocharacter's specification. Then
`parabolicRootPresentationOfDynamicRealization` supplies the actual compatible
presentation for the original component map, using the same two equalities.
Thus simultaneous realization is derived from the two dynamic structural
inputs rather than assumed separately in this construction.

`parabolicRootPresentationExistenceStatement_of_dynamic` introduces exactly
the arbitrary field, connected reductive group and supplied maps of the
published existence target and places this constructed presentation in
`Nonempty`. The theorem's conclusion is the unchanged universal existence
proposition, conditional on the displayed four statements. All subgroup-functor
equalities retain every test scheme, including nonreduced tests.

`parabolicRootPresentationExistenceStatement_of_dynamic_centralizer` uses the
published `dynamicGeometricUnipotentRadical_of_centralizer` to replace the
geometric-radical input by `DynamicCentralizerReductiveStatement`. This variant
retains the same number of explicit structural inputs and establishes none of
them independently. It preserves the full geometric greatestness clauses
supplied by that published reduction.

The provenance is composition of the two supporting construction modules and
the published dynamic-radical reduction. Worker 1491 authored the reused
simultaneous-realization argument; Worker 1294 authored its choice interface,
the presentation reduction and this assembly. No new external source assertion
is introduced. The simultaneous-realization and presentation-reduction pairs
included as dependencies are unchanged from their focused candidates.
