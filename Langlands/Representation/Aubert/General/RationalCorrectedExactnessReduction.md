# Actual rational corrected exactness from five explicit inputs

Author: Worker 691. This internal reduction specializes
`CorrectedExactnessReduction` to the literal rational-point families.
It derives the finite Coxeter, Levi, association and cardinality inputs
from published results and the original target premises. It makes no
new assertion from the literature and does not prove the unconditional
corrected Aubert Theorem 3.6.

`RationalCorrectedExactnessInputs` is a data type with five explicit fields:

- `bruhat : RationalBruhatStatement`;
- `gradedVanishing : RationalCorrectedGradedVanishingStatement`;
- `gradedTransition : RationalCorrectedGradedTransitionStatement`;
- `inductionJacquet : RationalSupportCategoryInductionJacquetStatement`;
- `exactnessDetection : RationalSupportCategoryExactnessDetectionStatement`.

The module constructs no inhabitant of these fields.

`parabolic_empty_eq_dynamic_of_standardCocharacter` uses the original
`StandardCocharacterStatement`, connected reductivity, a maximal split
torus and the generic defining cocharacter. The defining cocharacter
is standard at the empty face, by the published
`isStandardCocharacter_empty_self`. Thus the standard-cocharacter equality
at this face identifies the literal empty-index point parabolic with
the dynamic parabolic of that cocharacter.

`standardBruhatCover_of_rationalBruhat` additionally assumes the original
standard-parabolic order statement, point-normalizer comparison and
`HasRationalBruhatDecomposition i ν`. Its conclusion is
`IsBruhatCover (torusPoints i) (parabolic i ν ∅) (parabolic i ν J)` for
every standard index `J`. It takes the three factors from rational Bruhat
covering, transports the normalizer representative through
`normalizerEquiv`, identifies both parabolic factors with the empty
standard parabolic, and includes the right one in `P_J` by monotonicity.
No endpoint-statement premise is used.

`rationalIsExactBeforeTerminal_of_inputs` assumes the five fields as a
single data value. It applies to every connected reductive group scheme
over a nonarchimedean local field, every maximal split torus, generic
cocharacter and original structural hypotheses of
`RationalCorrectedTheorem36Statement`, with its endpoint-statement premise
omitted. The conclusion is exactness before the literal terminal degree
for every actual smooth `E ∈ Alg({I})`.

The proof constructs the actual finite point Coxeter system from
`rootSpanPointCoxeterData` using the given actual relative root system.
Its root-sign length law gives the positive simple-reflection comparison
by `positiveSimpleReflectionComparison_of_rootLength`, and its actual
Levi Weyl comparison is already a field of that data.
The assumed rational graded statements apply to this same system.
Association preserves cardinality by `rootAssociation_card_eq`;
support membership is transported by the published
`rationalSupportCategoryAssociationInvariance`.
The Bruhat field and the cover lemma give every needed filtration cover.
The other two supplied fields give induction--Jacquet stability and
exactness detection. These eight inputs form
`JacquetComplex.CorrectedExactnessInputs`, and
`JacquetComplex.isExactBeforeTerminal_of_inputs` concludes actual
normalized-complex exactness.

`rationalCorrectedTheorem36_of_inputs` concludes the exact published
`RationalCorrectedTheorem36Statement` from the same five-field value.
It introduces the target's endpoint premise and applies the stronger
preceding theorem.

The field universe and representation universe are independent (`u`,
`v`). Representations have precisely the target carrier universe
`max (u + 1) v`; no finite-length, admissibility or irreducibility
restriction is imposed on `E`. Empty roots and full terminal index are
included. The original terminal cokernel is retained. All five remaining
global fields must still be proved before these results can establish
the unconditional target.
