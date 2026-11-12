# Compact open containment for upper-unipotent groups over local fields

Author: Worker 5165. This is an internal construction derived from the published
`UpperUnipotentCompactContainmentProof` of Worker 201 (with Worker 117).

`localFieldUpperUnipotentCompactOpenSubgroup F n C hC` chooses an actual compact
open subgroup containing the entire supplied compact subset C. Its return type
includes both compactness and containment. F is any nonarchimedean local field,
with its supplied topology and valuation; positive characteristic and all ranks
are included. No canonical topology is substituted.

The implementation reuses the published all-field common-denominator lemma and
adapts the published private diagonal calculation. For positive rank it clears
one denominator simultaneously for all entries of C and its inverses. Conjugating
by diag(d^(-i)) makes these matrices integral. The preimage of the actual integral
GL subgroup under conjugation restricted to the upper group is the desired open
subgroup. It is compact because the upper group is closed and conjugation is a
homeomorphism. The field is Hausdorff by its compatible nonarchimedean local-field
topology. At rank zero the whole group is finite.

`localField_upperUnipotent_isLimitOfCompactSubgroups` forgets openness and the
chosen witness to give the published localization predicate. The corresponding
mirabolic-upper theorem transports compact sets and subgroups along the published
continuous multiplicative equivalence, retaining the inherited topology.

This module is an internal generalization of that published proof: every field
operation, denominator argument and compactness input there was already generic;
only its theorem header required PadicField. It does not depend on the old
p-adic containment conclusion. It constructs no derivatives and proves no
mirabolic restriction injectivity. The original Library Lean/Markdown pairs
are unchanged.
