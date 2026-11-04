# Actual scalar characters for the two Jacquet images

This internal construction supplies the existing
`Langlands.Aubert.General.InductionTwoJacquetScalarCharacters` data from
admissible Schur on the actual inducing representation and the second actual
normalized Jacquet image of its normalized induction. Both objects are assumed
irreducible and admissible. The ambient group is locally compact and
nonarchimedean; its universe `uG` and the inducing carrier universe `uV` are
independent.

The inputs include two semidirect decompositions `P = M U` and `Q = L O`,
closedness of both unipotent subgroups, and a smooth complex representation
`σ` of `M`. No relation between the two parabolics is required in this unit.
The second object is literally
`(jacquetFunctor hO hOc).obj ((normalizedInductionFunctor h hU).obj σ)`,
whose carrier universe is `max uG uV`.

`inductionTwoJacquetScalarCharactersOfSchur` chooses the full abstract-center
characters supplied by `Langlands.admissibleSchur_centralCharacter` on these
two objects. It retains their scalar-action equations in the existing data
structure from `TwoJacquetFactorExponents.lean`. The two
`inductionTwoJacquetScalarCharactersOfSchur_*_isOpen_ker` theorems use the
same chosen characters' locally constant functions: their fibers over `1`
are open and equal the respective kernels. No new character interface or
character-extension premise is introduced.

`nontrivial_induction_of_irreducible_secondJacquet` needs only
irreducibility of the second actual Jacquet image. The published
`repLength_eq_one_iff` and `repLength_pos_iff` give its nontriviality.
Its carrier is the actual `Jacquet.Localization.Coinvariants` quotient, so
surjectivity of `Jacquet.Localization.mk` forces the inducing ambient module
to be nontrivial. The proof uses no finite-length-preservation assertion for
induction and needs no induction-evaluation nonvanishing argument.

For any supplied `InductionTwoJacquetScalarCharacters` data, the two theorems
`InductionTwoJacquetScalarCharacters.first_norm_ambientCenter_eq_one` and
`InductionTwoJacquetScalarCharacters.second_norm_ambientCenter_eq_one`
deduce unit modulus on the ambient center from a supplied
`UnitaryCentralCharacter` on the actual induction. Each retains the appropriate
ambient-center containment, in `M` or `L`. The first uses the nontriviality
just proved and
`norm_inducingScalar_ambientCenter_eq_one`; the second uses nontriviality
of the second Jacquet image and `norm_jacquetScalar_ambientCenter_eq_one`.
Those comparisons are implemented in `CentralCharacterInheritance.lean`.
The second comparison uses `hO.levi_le_normalizer`, the containment used by the
actual `jacquetFunctor` definition.

The provenance is an internal deduction from the published admissible Schur
proof, representation-length/nontriviality equivalences, actual quotient-map
surjectivity, and actual scalar-action comparisons. These proofs make no use
of Langlands classification, character independence, the geometric lemma,
adjointness, or a cuspidal-support theorem.

Admissibility and irreducibility of the two objects remain explicit inputs.
This unit does not construct the two Jacquet factors, identify their characters
by conjugation, compare their signs, or establish unit modulus on an entire
Levi center. It supplies character inputs for subsequent sign arguments and
does not prove `RationalRankOneSelfAssociationStatement`.
