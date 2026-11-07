# Actual compact covariance of whole local enveloping actions

For an actual `OperatorRealization F n` over a number field `F : Type u`,
this module constructs the conjugated real-place and complex-place
universal enveloping algebra actions on the original `S.Space`. The maps
`realPlaceCompactConjugatedEnvelopingAction` and
`complexPlaceCompactConjugatedEnvelopingAction` conjugate the entire
original local differential by the actual corresponding compact
translation. They are unital complex algebra homomorphisms into the
original endomorphism algebra.

Each map equals the original local enveloping action composed with
`unitaryMatrixEnvelopingConjugation` of precisely the supplied orthogonal
or unitary matrix. These equalities hold as algebra homomorphisms, so they
cover every local enveloping element rather than only Lie generators.

For every full actual compact coordinate product, compact translation of
a local enveloping differential equals the differential of its actual
selected-place matrix enveloping conjugate followed by that translation.
The same compatibility holds as equality of endomorphisms under original
compact conjugation. Both identities follow by specializing the genuine
global compact/enveloping covariance and the proved global/place
whole-algebra inclusion compatibility.

Specializing the full product to an actual single-place insertion gives
same-place covariance. At every other infinite place the selected matrix
is the identity and its actual enveloping adjoint is the identity. This
proves commutation between each compact operator and every enveloping
operator at a distinct place, for both same-type and both mixed-type
orders. The same-type cases explicitly retain the inequality of places.
The proofs retain the original coefficient carrier and operators.

This internal construction reuses `PlaceCompactCovariance`,
`PlaceEnvelopingAction`, `ArchimedeanPlaceEnvelopingAdjoint` and the actual
global compact differential compatibility. It adds no source assertion,
topology or normalization. Complex coefficients, all natural ranks and
the arbitrary number-field universe are retained. Complex-place factors
continue to use the full underlying real matrix Lie algebra before
complexification. Irreducible local factors, admissibility, tensor
factorization, unitary realization and Langlands attachments remain
separate obligations.

The local additive-group instances have explicit module-specific names and
retain the original submodule additive structures, allowing this module and
the two-place tensor-action branch to be imported in the same environment.
