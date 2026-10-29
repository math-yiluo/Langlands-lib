# Full normalized reversal inside a product Levi

Worker 514 constructs the full representation equivalence needed to transfer
an upper geometric piece into an opposite piece. For an outer shape `B` and
refinement `S`, `reverseRefinement B S` reverses the inner blocks separately
inside each outer block. The actual element `reverseWeyl B S R` is the tuple
of inner block-reversal matrices.

`refinedLeviReverseEquiv B S` relabels every inner Levi by reversing its block
labels, using the existing concrete product-to-subgroup equivalences.
Conjugating its value by the blockwise reversal recovers the original
refined-Levi element. The same conjugation takes the upper unipotent subgroup
for the reversed refinement onto the opposite unipotent subgroup for `S`, using
`Langlands.Exponents.RefinedOppositeConeReversal.conj_mem_refinedOppositeUnipotent_iff`
from the existing exponent-reversal module.

`refinedReverseCoinvariantsEquiv` is the actual linear equivalence between
these two coinvariant quotients. It sends the class of `v` to the class of
`ρ (reverseWeyl B S R) v`. The inverse uses the inverse matrix. Both maps
descend by the proved subgroup-conjugation identity; their compositions are
the identity on quotient representatives.

Over an actual p-adic field, the full refined modulus of a reversed-label
Levi element is the inverse of the original full refined modulus. This
follows factor by factor from the published `leviModulus_reverse` identity.
Consequently the upper inverse half-modulus equals the opposite
normalization after relabelling.

`normalizedRefinedOppositeReverseEquiv` identifies the reversed upper Jacquet
representation pulled back along `refinedLeviReverseEquiv` with the opposite
Jacquet representation along `S`. It intertwines the action of every
refined-Levi element, and its formula on quotient representatives is the
translation formula above. No smoothness, admissibility, irreducibility or
finite-dimensionality hypothesis is used. The field and representation
carrier universes remain independent.

The provenance is internal algebraic conjugation and composition of the
published refinement definitions, block reversal, explicit modulus and
coinvariant constructions. This module does not prove a geometric lemma,
identify a geometric filtration grade, select a branch, or prove the
supported branch obstruction.
