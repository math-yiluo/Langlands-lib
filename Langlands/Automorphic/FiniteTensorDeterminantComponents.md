# Local components of the genuine determinant-twisted presentation

For a number field of arbitrary universe, every natural rank, independently
universe-polymorphic complex local modules, a genuine finite tensor
presentation of a nonzero actual finite form space, and a finite-order
Hecke character, this internal construction compares two actual local
subspaces. The first is the local component chosen from the new genuine
global determinant-twisted presentation. The second is the actual
determinant image of the old presentation's chosen local component.

`determinantTwistPresentationLocalComponentEquiv` is an equivariant
complex-linear equivalence between these local subspaces. Both are
equivalent to the same specified local factor with its positive scalar
twist by the actual local determinant character. Composing those
equivalences gives the comparison. Nonzeroness of the new global space
follows from the established injective multiplier.
`determinantTwistPresentationLocalComponentClass_eq` therefore identifies
their existing smooth representation classes, in the universe of actual
forms. It asserts no equality of their embeddings or chosen complementary
vectors.

`determinantTwistLocalComponent_exists_integral_fixed_outside` proves a
nonzero vector fixed by the actual integral completed-local matrix group
outside the union of the original tensor exceptions and the proved
character-tail bound. It applies the existing conditional fixed-vector
transport and discharges its character-triviality hypothesis with the
full-tail theorem. The cofinite-filter theorem gives the corresponding
almost-everywhere assertion.

Provenance is internal composition of the genuine twisted tensor
presentation, its local-component equivalence, the actual multiplied
local-component equivalence, finite character-tail triviality, and the
existing fixed-vector transport. No new factorization or occurrence
assumption is introduced. These results provide no Hecke eigenvalues,
Satake parameters or almost-everywhere Weil/Galois matching.
