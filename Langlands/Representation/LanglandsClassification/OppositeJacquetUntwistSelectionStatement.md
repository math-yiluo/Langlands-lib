# Selecting a tempered untwist of an actual opposite Jacquet exponent

Worker 148. `OppositeJacquetUntwistSelectionStatement` is an internal,
closed proposition isolating the remaining exponent-selection obligation
in the opposite-Jacquet proof of Langlands exhaustion. It is a statement
only; this module proves no existence assertion.

For every connected reductive group over a nonarchimedean local field, it
uses the canonical ambient point topology with the stated local compactness
and nonarchimedean group assumptions. It fixes exactly the torus, generic
cocharacter, reflection data, maximal split torus and minimal parabolic
witnesses used by `LanglandsQuotientExhaustiveStatement`. For every
irreducible smooth ambient representation it requires an actual opposite
standard Jacquet exponent and its `UnitaryUntwist` record.

The untwist must be `IsNormalizedExponentTempered` on the original standard
Levi with its canonical topology. The actual exponent's real part must lie
in `restrictedCorootChamber` for its original standard index, split
component and component factor. No quotient map is assumed. The field
universe `u` and original representation-carrier universe `v` are independent.

The provenance is internal: this is the exact remaining selection input
needed by `OppositeJacquetExhaustionReduction`. The published opposite
Jacquet family and unitary-untwist record supply the actual objects and
types, without establishing the selection. The maximal-exponent,
structural decomposition and nested Jacquet arguments remain obligations.
