# Single-place compact actions on the original automorphic realization

For a number field `F : Type u`, every natural rank `n` and an existing
`OperatorRealization F n`, this module restricts its actual compact action
to the orthogonal group at a real infinite place and to the unitary group
at a complex infinite place. The coefficient field is complex and the
carrier remains the original `S.Space`. The source groups are
`Matrix.unitaryGroup (Fin n) ℝ` and `Matrix.unitaryGroup (Fin n) ℂ`;
the real unitary condition is the existing orthogonality condition.
Rank zero is allowed.

`realPlaceCompactRepresentation` and `complexPlaceCompactRepresentation`
compose the existing `S.compactRepresentation` with the actual continuous
injective group inclusions from `ArchimedeanPlaceCompact`. The restricted
representations are ordinary algebraic representation objects; no new
continuity assertion about their endomorphism-valued maps is made.

The inclusion identities show that the action is the original compact
translation on the embedded stable automorphic functions. The evaluation
identities compute that same action on its original adelic function:
the argument is multiplied on the right by the inserted compact element.
The inclusion has the selected matrix at the specified place and identity
at every other place, by the prerequisite's coordinate formulas.

Finite adelic translations commute with both place compact actions.
This is the existing finite/full compact commutation identity specialized
to the actual place inclusion. Every vector is finite for either place
compact action. The proof places its place orbit span inside its original
full compact orbit span, which is already proved finite dimensional,
and uses finiteness of a subspace. No irreducibility or finite dimension
of the ambient realization is assumed.

The covariance identities act on every original global complex Lie
direction. They use the actual global adjoint of the inserted compact
element, by specialization of the existing compact/Lie covariance
theorem. These identities do not identify that adjoint with a separately
defined local matrix adjoint.

Full automorphic intertwiners and equivalences restrict to genuine
intertwiners and equivalences of these place actions. The underlying
linear maps and linear equivalences are unchanged; their compatibility
is the original full compatibility evaluated on the inserted compact
operator.

This is an internal construction using `OperatorCompactCompatibility`,
`OperatorEquivalence`, `ArchimedeanPlaceCompact`, the actual orbit span in
`Representation/FiniteVectors` and pinned Mathlib's subspace finiteness
result. No additional assertion from original literature is used.

No irreducible archimedean automorphic factor, tensor factorization,
local Langlands attachment, or local matrix adjoint identification is
constructed here. Those remain separate obligations.
