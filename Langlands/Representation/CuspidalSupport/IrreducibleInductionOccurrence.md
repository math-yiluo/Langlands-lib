# Actual cuspidal occurrences and irreducible induction

Worker 1216. This internal helper connects the published actual cuspidal
constituent theorem with normalized first adjointness. It is intended for the
local identification step of adjacent cuspidal Jacquet interchange.

An irreducible admissible smooth object `X` has an actual irreducible cuspidal
subquotient `D` in its normalized Jacquet module. If normalized induction of `D`
is irreducible, `irreducibleInductionIsoOfCuspidalOccurrence` constructs an
isomorphism from `X` to that induced object. Jacquet admissibility and the
published cuspidal constituent theorem first upgrade the actual occurrence to
a surjective Jacquet intertwiner. Irreducibility makes its target nonzero.
Normalized first adjointness gives a nonzero map from `X` to induction of `D`.
Schur's elementary injectivity and surjectivity arguments make this a
bijective intertwiner and hence an actual smooth isomorphism.

`isQuotient_normalizedJacquet_of_inductionHom` uses evaluation at the identity
to descend a nonzero map into induction to a nonzero Jacquet intertwiner.
Irreducibility of its target makes that intertwiner surjective. Its conclusion
is the actual smooth quotient relation.

`cuspidalOccurrence_transfer_of_inductionIso` composes the constructed
isomorphism with a supplied isomorphism of induced objects. It applies the
preceding quotient result for the target block shape, then regards that
quotient as an actual subquotient. The target inducing object need only be
irreducible; this step requires no target cuspidality assumption.

The field and representation universes are independent; all smooth carriers
here lie in `Type (max uF uV)` to match the normalized induction codomain.
This module does not perform coarse constituent extraction, identify adjacent
inner shapes with the binary product, or prove the whole interchange theorem.

This is derived internal infrastructure. Its mathematical inputs are the
published `leviCuspidalConstituentTheorem`, the elementary normalized Jacquet
admissibility adapter
`FiniteLengthAssembly.isAdmissible_normalizedJacquet`, the concrete
`Parabolic.FirstAdjointness.equiv`, `jacquetEvaluation_ne_zero`, and Mathlib's
irreducibility results for actual intertwiners. The quotient-to-subquotient
conversion is `SmoothRep.IsQuotient.isSubquotient`. No original literature is
claimed to state this interface verbatim.

The transitive project import closure was traversed from all four direct
imports and contains 316 project modules, with no unresolved project import.
Its classification modules are `Supercuspidal`, `SupercuspidalSupport`,
`Segments`, `SupercuspidalTwist`, `ConstituentRelations`,
`SupercuspidalContragredientAux`, `SupercuspidalContragredientStatement`,
`FiniteLengthStatement`, and `FiniteLengthProof`. These provide definitions,
elementary isomorphism/subquotient transport, and lower finite-length results.
The admissibility adapter used here depends on the normalized Jacquet
admissibility theorem; the other finite-length conclusions in its module are
not used by this proof.

Neither the closure nor the implemented proof uses the conclusions or proof
successors of analytic segment classification
(`aca8805b-054f-4d56-8045-12db7f623404`), multisegment exhaustion
(`3bfb61fa-1129-4fc9-83fd-7fcfec22106e`), ordered strong-head existence
(`ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`), ordered quotient coverage
(`20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`), tempered block uniqueness
(`52e97845-36bb-457d-b76f-70753334b88c`), square-integrable Langlands
classification (`1cb45da2-7007-4351-a694-594fb148b8d1`), square-integrable
exhaustion (`cd8ab97c-0b78-4bce-97c4-d307a28159a4`), or regular exhaustion
(`bf433f0a-921a-428c-b0c0-6475438125ac`). In particular, the local occurrence
is upgraded by the already published cuspidal constituent theorem and concrete
adjointness, with no disjoint-support decomposition or classification input.
