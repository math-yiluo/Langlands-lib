# Monomial expansion retaining the normal abelian subgroup

Worker 1787 strengthens the published Anthropic monomial engine by retaining its
initial normal abelian subgroup A inside every inducing subgroup. This is an
internal supporting lemma for finite degree-zero Brauer induction. The copied
proof portions derive from the Anthropic FLT monomial solution at commit
6e837e75355538c7f80bab5b956861e86c4eacc2 (Copyright 2026 Anthropic, PBC,
Apache-2.0); see the repository notices. The original helper lemmas are imported
from the published Library and remain unchanged.

The extra invariant uses the fact that an occurring weight of B is a scalar
character, hence fixed by conjugation by B. The enlarged subgroup B contains A,
so its weight stabilizer contains A. The recursive expansion retains the
subgroup of A inside that stabilizer; mapping subgroups back retains A itself.
Commuting actions use only the full subgroup; direct sums concatenate the lists.
No degree-zero generation conclusion is assumed here.

`Monomial A W σ` means that a finite list of actual subgroup/unit-character
data has normalized induced character sum equal to the trace of σ, with A
contained in every subgroup of the list. Both the group and the representation
carrier are in `Type 0`, as in the imported engine. This helper does not claim
arbitrary-universe degree-zero generation or an equality in `VirtualRep`.

`engine hp m K W σ hm A hcomm hpow` proves this predicate when A is normal
and commutative, every group element has some p-power in A, p is prime,
and `|K| + dim W ≤ m`. The artificial bound supports strong induction and
can always be chosen to be `|K| + dim W`. The retained subgroup may be trivial.
The existing `lsum` and `ClassFunction.induced` conventions are unchanged.

The proof retains the original two decreasing branches: either pass to a proper
weight stabilizer, or split into two nonzero invariant summands of smaller
dimension. `weight_fixed` proves the new containment needed in the stabilizer
branch using `weightHom` and commutativity of complex units. The copied trace
calculation uses only the already published weight-space and trace lemmas.
The finite degree-zero argument will separately compare these normalized sums
with actual induction using the published induction-character formula.
