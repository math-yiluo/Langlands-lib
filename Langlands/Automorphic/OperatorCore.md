# Concrete automorphic operators and their invariant core

This internal construction works on the published finite-smooth,
rational-invariant complex functions over any number field `F : Type u`,
at every natural rank `n`. It uses the actual finite adelic translations,
the actual standard infinite compact translations, and the genuine complex
enveloping differential action. It does not assume preservation of the whole
automorphic space under the last two families.

The operator algebra is their generated subalgebra inside the endomorphisms
of that concrete ambient space. Thus all operator identities already true on
the ambient functions remain true in this algebra; it is not a free algebra
or an arbitrary action supplied as a parameter.

For any complex subspace `P` of the ambient space, `operatorCore P` consists
of functions `f` such that `a f` belongs to `P` for every element `a` of the
operator algebra. This is constructed directly as a subrepresentation.
The identity operator shows that it is contained in `P`; composition proves
invariance. `le_operatorCore_iff` proves that it is the largest invariant
subspace contained in `P`. The zero core is allowed.

The invariance criterion `operator_invariant_iff` says that closure under the
three generator families is equivalent to closure under the entire algebra.
The reverse direction uses algebra-adjoin induction: scalar operators preserve
a complex submodule, and sums and compositions preserve any subspace stable
under their summands and factors.

Taking `P` to be the actual automorphic subspace constructs
`automorphicOperatorCore` and its carrier `StableAutomorphicFunctions`.
Its finite and compact actions are restrictions of actual positive right
translation; its enveloping action is restriction of the genuine differential
action. The latter remains a complex algebra homomorphism. The faithful
inclusion into actual forms intertwines finite translations, and smoothness
of the finite action follows from that inclusion.
The three `..._val` identities identify the restricted operators with the
ambient ones exactly. Finite translation commutes with the restricted
enveloping action by the published ambient commutation identity and
injectivity of the subtype inclusion.

`automorphicOperatorCore_eq_iff` identifies equality with the full form space
with the conjunction of the existing compact-translation and differential
preservation statements. Finite translation is already known to preserve all
forms. The proof converts the smooth-function and finite-smooth presentations
of the same forms using their published equivalence. This is a conditional
characterization, not a proof of the two remaining preservation obligations.

This unit supplies a maximal concrete invariant space, with its universal
property and genuine actions. It asserts neither its nonzeroness nor equality
with all forms. Irreducible realizations, cuspidal classes, subquotients,
admissibility, tensor factorization, spectral existence and isobaric
classification are not constructed here. It does not claim a comparison
with the full archimedean Hecke algebra or a new differential covariance
theorem. These boundaries retain the existing analytic and representation
obligations.

All content is derived from the published `FiniteRealization`,
`PreservationStatement`, and their concrete ambient actions, together with
Mathlib's generated-subalgebra and subrepresentation constructions. No new
assertion of correspondence to an original-literature passage is made.
