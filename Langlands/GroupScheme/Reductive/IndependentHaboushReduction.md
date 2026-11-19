# Conditional Haboush assembly with split-cover and Steinberg inputs

Worker 589, with Worker 169's cover helper, Task 7298. Helper module of
`IndependentGeometricReductivityProof`, which discharges both premises.

The module proves a conditional implication from the existing Library
propositions `SplitSimplyConnectedCoverExistenceStatement.{u}` and
`SteinbergBigCellStatement.{u}` to the unchanged
`ReductiveGeometricReductivityStatement.{u}`, at every universe `u`.
It also proves
`IndependentHaboush.reductiveGeometricReductivity_of_rootDatum_and_bigCell`:
`RootDatumExistenceStatement.{u}` and `SteinbergBigCellStatement.{u}` imply the
same target. Neither implication discharges its premises here. The module
`IndependentGeometricReductivityProof` proves both premises from the rank-one
central cover and states the exact target with no added premise.

The implemented proof reuses the generic clean parts of
`GeometricReductivityReduction`: descent of invariant polynomials along a
central isogeny, the central split-torus zero-weight projection and transport
along an isomorphism of central tori. In positive characteristic it uses the
published central-derived product and finite central intersection to obtain a
semisimple derived factor. Over the algebraically closed field a split maximal
torus exists. The explicit split-cover premise then supplies its simply
connected cover; no arbitrary-field cover descent is used.

The explicit Steinberg premise enters only through
`simplyConnectedPositiveCharConjugationMap_of_bigCell`. Finite regular
coordinates and linear pullback carry the separator back to the original
representation. In characteristic zero the existing Lie-algebra complete
reducibility proof supplies a degree-one separator. All polynomial invariance
conclusions keep arbitrary relative test schemes, including nonreduced and
nonaffine tests.

This is an internal derived assembly of existing generic reductions. Its
positive-characteristic structure parallels the existing Haboush assembly,
but its formerly excluded cover and canonical-rho calls are explicit premises;
there is no invocation of the old `reductiveGeometricReductivity` or its
structural arguments. A full type/value dependency audit passed on 17 November 2026, reaching
23,386 project constants and no excluded statement or known contaminated
implementation name (diagnostic `3ab3d04c-d36a-4ef5-8a0f-691b652860eb`).
The mathematical module compiled successfully in diagnostic
`3042b0e5-a1ee-4fae-8630-3221dc7ee351`. These private compiler diagnostics do
not supply independent semantic acceptance or prove the two premises.
The root-datum premise comes from Task 7458's reducedness theorem and the
Steinberg premise from Task 7459's structural inputs, both applied to the
rank-one central cover in `IndependentGeometricReductivityProof`.

The root-datum version composes the original assembly with Worker 169's
`splitSimplyConnectedCoverExistence_of_rootDatumExistence`. That helper applies
the existing minimal-lattice cover reduction with the Library proofs of
central-isogeny root-datum transport and semisimple perfectness. These inputs
have separately passed a type-and-value dependency audit (diagnostic
`67e07da0-f706-4b94-b7de-feb9cf64f46a`). This composition is a derived
conditional theorem; it proves neither premise.
The helper and the composed assembly compiled together in diagnostic
`d164944e-c18d-4605-881f-5d6dd69346f2` on 17 November 2026.
