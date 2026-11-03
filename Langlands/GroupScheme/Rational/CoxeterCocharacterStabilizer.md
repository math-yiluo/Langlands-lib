# The actual Weyl stabilizer of a standard cocharacter

This internal supporting module defines the stabilizer of pairing with a cocharacter
under the actual scheme relative-Weyl character action. For a standard
cocharacter, its stabilizer is the standard Coxeter subgroup of the face.
One containment uses the realization's actual standard-Levi clause and the
published pairing invariance for points of a dynamic centralizer. For the
other, choose a right descent. Its simple root has negative image, with an
actual opposite root supplied by the same simple reflection. Nonnegativity
of pairing on positive roots forces the descent label into the selected face.
Induction on Coxeter length finishes the containment. No global negation
stability of the relative roots is assumed in this argument.

The provenance is internal: these are consequences of the published
`IsRelativeWeylCoxeterRealization`, `IsStandardCocharacter`, actual Weyl action,
`latticePairing_weylAction_of_mem_dynamicCentralizer`, positive-root induction,
and Mathlib's Coxeter descent and length theorems. The all-test twisted-Levi
intersection remains a separate obligation.

The declarations are `cocharacterPairingWeylStabilizer`,
`IsRelativeWeylCoxeterRealization.simple_action_self`,
`IsRelativeWeylCoxeterRealization.standardSubgroup_le_pairingStabilizer`, and
`IsRelativeWeylCoxeterRealization.pairingStabilizer_eq_standardSubgroup`.
The equality needs a generic cocharacter, a supplied realization, and a
standard cocharacter for the finite selected face. It does not require
finiteness of the whole simple-root type or reductivity. The descent proof
uses `CoxeterSystem.exists_rightDescent_of_ne_one`, the realization length/sign
clause, `schemeWeylCharacterAction_mem_relativeRoots`,
`IsStandardCocharacter.pairing_nonneg_of_positive`, and induction on length.
