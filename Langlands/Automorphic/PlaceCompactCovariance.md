# Actual place compact and Lie covariance on automorphic realizations

For a number field `F : Type u`, natural rank `n` and an existing
`OperatorRealization F n`, this module proves compatibility between the
actual compact and complexified Lie actions at the infinite places.
It retains the original `S.Space`, complex coefficients and arbitrary
number-field universe. Rank zero is allowed. The complex-place Lie domain
is the complexification of its full underlying real matrix Lie algebra.

The full compact product identities specialize the existing global
compact/Lie covariance to the original place inclusions, then apply the
proved global/local matrix adjoint comparison. Thus the action of any
full compact product on a place Lie operator is the Lie operator of the
actual matrix adjoint in that coordinate, followed by the same original
compact translation. Invariance of the place Lie algebra is proved in
the global prerequisite, rather than assumed here.

The same-place identities restrict the full compact product to an actual
single-place compact inclusion. Their Lie direction transforms by
`unitaryMatrixComplexLieConjugation` of that very orthogonal or unitary
matrix. At a distinct place, the inserted compact matrix is the identity,
so its adjoint is the identity. This proves commutation both between
opposite types of infinite place and between distinct places of the same
type. A private tensor-induction argument proves that the actual
complexified adjoint of the identity matrix fixes every Lie direction.

`realPlaceCompactEndConjugation` and
`complexPlaceCompactEndConjugation` are actual algebra automorphisms of
`Module.End ℂ S.Space`, obtained by conjugating with the original
invertible compact translation. Their inverse uses the inverse compact
translation. The finite-operator identities show that these algebra
automorphisms fix every finite adelic translation operator, by the
already proved full compact/finite commutation and conjugation laws.

This is an internal construction using `PlaceLieAction`,
`PlaceCompactAction`, `ArchimedeanPlaceAdjoint` and the original full
compact covariance and endomorphism conjugation. All actions and
adjoints are constructed on their actual original carriers. No new
source assertion, topology or normalization is introduced. This module
does not extract irreducible archimedean factors, assert their
admissibility, or construct a local Langlands attachment.

The module's local `AddCommGroup` instances have explicit names
(`placeCompactCovariance…AddCommGroup`), for the same reason as in
`PlaceCompactAction`: automatically generated names of unnamed local instances
can coincide across modules and block joint imports. Worker 8 made this change
in task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. The instances are unchanged
(`Submodule.addCommGroup _`), and no other declaration changed.
