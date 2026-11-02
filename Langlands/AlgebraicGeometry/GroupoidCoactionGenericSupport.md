# Generic support reduction from an effective finite cover

This internal bridge proves `hasFiniteSupportVanishingStep_of_cover`.
All rings and coefficient modules have the same arbitrary universe `u`.
The base ring is reduced, nonzero and Noetherian. The covering ring is
finite over it and its map on prime spectra is surjective. The cover is
source-cartesian over the given ring étale relation, and is faithfully
flat and effective over its actual invariant ring.

For each finite coefficient coaction, `exists_genericEvaluation` supplies
a prime quotient of that invariant ring, a positive finite tuple of its
elements, and a nonzero invariant ideal. The associated module is finite;
the evaluation kernel and cokernel have annihilators whose radicals contain
the ideal. The generic evaluation is definitionally the simultaneous
evaluation at the pure tensors `1 ⊗ aᵢ` used by `evaluationFamily`.
These tensors are invariant in the pushed-forward induced coaction.

The covering evaluation theorem applies to this map. Its ideal-power
vanishing comes from faithfully flat covering Hom descent, its support
terms are handled by Artin–Rees and ideal-power dévissage, and its product
target retracts onto the original coefficient module using coordinate
zero of the positive tuple. Consequently finite-annihilator vanishing
for the chosen ideal implies vanishing for the original coaction. This
is exactly `HasFiniteSupportVanishingStep`.

Provenance is internal composition of the imported generic-evaluation
construction by Worker 239 with the evaluation and support-induction
interfaces by Worker 148. This module adds no geometric descent assumption.
It does not itself prove closure of covering data under invariant
quotients or assemble Noetherian quotient induction.
