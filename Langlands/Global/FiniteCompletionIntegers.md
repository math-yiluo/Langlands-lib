# Canonical integers of the original finite completion

This internal comparison uses the original number-field finite completion
`FiniteCompletion F v`, in an arbitrary universe, with its existing topology.
It uses the valuative relation `FiniteCompletion.valuativeRel v`, defined by the
original completion valuation in `FiniteCompletionLocalField`. The comparison
does not replace the completion or install a new global topology or valuation
instance.

`mem_canonicalIntegers_iff` identifies the elements of its canonical valuation
ring `𝒪[FiniteCompletion F v]` with the original
`v.adicCompletionIntegers F`. The canonical valuation is compatible with that
valuative relation, so its inequality against one is exactly the inequality
for the original completion valuation. Extensionality gives equality of the
actual subrings in `canonicalIntegers_eq`.

`canonicalIntegersEquiv` is the ring isomorphism induced by that subring
equality. Both it and its inverse leave the underlying completion element
unchanged. `canonicalIntegersHomeomorph` uses the same underlying equivalence
and proves continuity in both directions, using the subtype topologies from the
original completion. `canonicalIntegersEquiv_algebraMap` states that the
actual inclusions into that completion commute with this comparison.

`canonicalResidueEquiv` is the induced ring isomorphism between the actual
residue fields. `canonicalResidueEquiv_residue` proves compatibility with the
actual reduction maps. Thus this comparison retains the supplied residues,
rather than identifying fields only by their cardinality.

All results follow directly from the existing completion valuation,
valuation-ring definitions, and Mathlib's subring and residue-field
isomorphisms. They provide coefficient comparisons for later integral-model
arguments. They do not prove reductive-model existence, integral maximality,
local parabolic covering, or the host Iwasawa-family existence statement.
