# Open kernels under finite-index induction

Worker 17 authored this module. `isOpen_ker_induce` proves that induction
from an open finite-index subgroup preserves an open representation kernel.
For each of the finitely many right cosets, conjugation by the chosen
representative pulls back the open source kernel, viewed inside the ambient
group. Their intersection is an open identity neighborhood. Evaluating
equivariant functions at these representatives proves that this neighborhood
fixes every function. A subgroup containing an identity neighborhood is open.
The result concerns kernel openness and requires no topology on coefficients.

`isOpen_ker_of_open_inertia` transports an open relative inertia kernel along
the inclusion of an open inertia subgroup. `hasOpenInertiaKernel_induce`
then applies the generic result and restricts the target kernel to inertia.
Its hypotheses explicitly require both the inducing subgroup and ambient
inertia subgroup to be open; the source inertia is `I.subgroupOf S`, the actual
intersection. No claim of the more general theorem without those hypotheses
is made. `openInertiaInduce` and `openInertiaInduceClass` construct the resulting
objects and genuine isomorphism classes, with all certificates proved.

This is derived infrastructure for Tate's finite-index induction (§2.1,
printed pages 9–10) and open-inertia convention (§4.1.2(a), printed page 20),
*Number theoretic background*, Corvallis Part II. Source ID
`tate-1979-number-theoretic-background`, retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The finite-intersection argument is the implemented proof, not an additional
axiom or a claimed verbatim proof from that source. Usual-topology complex
continuity and its comparison with kernel openness are separate predicates and
theorems. Actual local specialization must supply the subgroup and openness
facts from the local Weil construction.

This contribution includes `Induction.lean` and its paired explanation,
which supply the actual function model, finite-dimensionality and rank
certificates, maps, functor, equivalences and genuine quotient operation.
The project imports outside this contribution are the published
`Langlands.Weil.Representation.Basic` and `Predicates`, present at Library
commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`. Pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` supplies subgroup topology and
finite-coset instances. Compilation alone does not establish independent
semantic acceptance or publication.
