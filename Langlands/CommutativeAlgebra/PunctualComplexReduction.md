# Reduction of the punctual complex theorem to two local algebra inputs

Author: Worker 1015.

The definition `punctualTopHomologyIsoOfLocalAlgebra` chooses an actual
`R`-module isomorphism `H^g(K) ≅ k` from the conditional theorem below.
It takes proofs of both supporting propositions and every original
pointwise punctual hypothesis explicitly. It uses `Classical.choice`
on the theorem's `Nonempty` conclusion, so this choice is noncomputable
and makes no claim of canonicity.

The theorem
`regularLocalPunctualComplex_of_acyclicity_of_residueResolutionDuality`
proves the implication
`RegularLocalFiniteLengthAcyclicityStatement →
RegularLocalResidueResolutionDualityStatement →
RegularLocalPunctualComplexStatement`
in every universe `u`. Both supporting propositions are explicit
hypotheses. This file supplies a conditional reduction; it supplies
neither supporting proof and does not prove the unconditional punctual
perfect-complex statement.

The proof takes all the original punctual hypotheses without alteration.
It chooses the existing `punctualMinimalModel`, a finite free complex
`M` supported in degrees `0` through `g`, together with its actual
homotopy equivalence to the original complex `K`. The induced homology
isomorphisms identify the annihilator ideals, so the given
maximal-ideal-power annihilation transfers to `M`.

The acyclicity hypothesis gives zero homology of `M` below `g`; its
upper term bound gives zero homology above `g`. The existing
`exists_pow_le_annihilator_homology_reversedDual` transports
maximal-ideal-power annihilation to the reversed dual `D`. Reversal
preserves finite freeness and takes the two term bounds to the same
interval. Applying the acyclicity hypothesis again shows that `D`
has no homology except possibly in degree `g`.

The existing first-order quotient argument, packaged as
`punctualModelReversedDualTopHomologyIsoResidueField`, identifies
`H^g(D)` with the residue field using the punctual hypothesis on the
ideals `J` with `m² ≤ J ⋖ m`. Thus `D` satisfies all premises of the
residue-resolution duality hypothesis. That hypothesis identifies the
top homology of the reversed dual of `D` with the residue field.
Finally, evaluation gives the existing complex isomorphism from `M`
to its twice reversed dual. Its homology isomorphism, followed by the
one just obtained and the homotopy-equivalence homology isomorphism,
gives `H^g(K) ≅ k`. The same homotopy equivalence transports the
vanishing in the other degrees.

This is an internal composition of the imported interfaces. It
introduces no new axioms, no change to the original target or its
imports, and no algebraic-geometry imports. The proof uses integer
degree bounds throughout and includes `g = 0` without a separate
case. The cited supporting statement modules document their
literature provenance and the remaining acyclicity and duality
proof obligations.
