# Proof of the fixed-exponent descriptions of temperedness

Authors: Worker 403 (original proof and documentation) and Worker 363
(current-base adaptation, explicit exported universe order and validation).

`Langlands.temperedLp` proves the closed proposition
`Langlands.TemperedLpStatement.{uG,uF,uV}`. Its component lemmas are
`Langlands.isTemperedModCenter_iff_forall_isLp` for a supplied quotient Haar
measure and `T.isTempered_iff_forall_isLp` for the canonical GL all-Haar
predicates. The group, field and carrier universes are independent. The closing theorem
explicitly declares those three universe parameters in the statement order.

For the generic forward direction, the proof retains the admissibility and
unitary central character from `IsTemperedModCenter` and specializes the
coefficient condition to the chosen positive `ε`. For the reverse direction,
the fixed-exponent hypothesis at `ε = 1` supplies admissibility and a central
character `c`. For each other positive `ε`, its fixed-exponent hypothesis gives
a potentially different character `d` and the required `MemLp` condition.
The published `UnitaryCentralCharacter.coefficientNorm_eq` identifies the
descended norms for `c` and `d`, so this condition holds with the single chosen
`c`. This proves the original existential character condition uniformly over
all positive `ε`.

The GL lemma installs exactly `T.topology`, its general linear topological group
instance, and the canonical central-quotient Borel instances used by both
predicates. It applies the generic equivalence for each Haar measure and
interchanges the universal measure and positive-exponent quantifiers.
There is no change of measure or of Borel realization in this argument.

The closing theorem assembles the two component lemmas. Their hypotheses match
the statement for arbitrary carriers, including zero carriers, and all natural
GL ranks. No character-existence, irreducibility, admissibility, carrier
countability or positivity premise is added.

This proof is internally derived from the existing analytic predicates, the
fixed-exponent definitions in `Classification/LpModCenter`, and the
character-independence theorem in `MatrixCoefficient/ModuloCenter`.
It invokes no original literature theorem or analytic integration estimate.
It proves a logical compatibility of the predicates, with no block tensor
comparison or final-task completion claim.
