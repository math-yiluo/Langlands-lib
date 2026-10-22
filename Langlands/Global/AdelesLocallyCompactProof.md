# Local compactness of number-field adeles

Author: Worker 108.

This proof establishes the published `Langlands.Global.AdelesLocallyCompactStatement K`
for every number field `K : Type u`, with no additional hypotheses. It preserves
Mathlib's restricted-product topology on `FiniteAdeles K` and product topology
on `Adeles K`. The internal argument is derived from published Library results
and Mathlib's compactness criteria.

## Implemented proof

First, the private lemma `normIntegers_eq_adic` identifies the norm valuation
subring `LocalGalois.baseIntegers (FiniteCompletion K v)` with the actual adic
integer ring `v.adicCompletionIntegers K`. Membership on both sides is equivalent
by `Valued.toNormedField.norm_le_one_iff` for the canonical rank-one norm.

The private lemma `compact_adicIntegers` transports the published
`CompletionResidue.finite_residueField` across this equality. The adic integer
ring is complete because it is a closed subspace of the complete adic field.
Mathlib supplies its discrete valuation ring instance. The complete discrete
valuation ring with finite residue field criterion in
`Mathlib.Topology.Algebra.Valued.LocallyCompact` then gives compactness.

The public theorem `finiteAdeles_locallyCompactSpace` equips each adic integer
ring with this compactness and uses `Valued.isOpen_valuationSubring` for openness.
Mathlib's additive restricted-product local compactness instance applies to
these compact open additive subgroups. This is the actual finite adele ring,
with its existing topology. The instance constructs compact neighborhoods by
translation, so no separate local compactness assumption on the fields is needed.

The public theorem `adeles_locallyCompactSpace` combines that result with
Mathlib's local compactness of the infinite adele ring, using the finite product
instance. Finally, `adelesLocallyCompact` has exactly the published local
compactness statement as its conclusion. Downstream proofs can install either
public compactness theorem locally as an instance.

## Scope and provenance

The target and its original-source correspondence are documented in the
published `Langlands/Global/AdeleQuotientStatement.md`. This module supplies a
derived proof via the published completion residue field theorem and Mathlib;
it does not introduce or change a mathematical definition or source statement.
It proves only the local compactness component. Discreteness and closedness of
the principal adeles and compactness of the quotient are separate obligations.
