# Actual exact duality commutes with restriction and finite-index induction

Worker 1763 derives these identities for fixed-Haar duality task
`e945d920-df9f-446c-9528-b488a3bee609`.

`continuousRestrict_continuousDual` identifies restriction of the actual
contragredient with the contragredient of restriction, along every supplied
continuous homomorphism of topological groups. Both sides act on the same
dual carrier. Preservation of inverses by the group homomorphism makes the
identity linear map an invertible intertwiner on genuine representations.
The universal property of the exact quotient gives the stated identity
on every continuous exact virtual class.

`continuousDual_induce` proves that exact duality commutes with the existing
exact induction from an open finite-index subgroup. The openness and proved
continuity theorem supply closure of the continuous objects under actual
induction. The proof reduces equality of integer-linear maps to genuine
representation classes, then uses the explicit `induceDualEquiv` from
`Weil/Representation/InductionDual`. This is the sum-of-coset-pairings
equivalence, not an assumed duality or a dimension-only identification.

The carrier universes are those of the existing maps, and all genuine
short exact relations remain imposed. There is no finite-image or
semisimplicity restriction. This is internal derived algebra from the actual
constructors and the explicit finite-dimensional comparison; it supplies no
local-constant functional equation or degree-zero generation theorem.
