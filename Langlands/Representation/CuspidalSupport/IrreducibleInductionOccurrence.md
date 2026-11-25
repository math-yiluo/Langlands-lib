# Actual cuspidal occurrences and irreducible induction

This internal helper connects the published actual cuspidal
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

Neither the closure nor the implemented proof uses the conclusions or
proofs of analytic segment classification, multisegment exhaustion,
ordered strong-head existence, ordered quotient coverage, tempered block
uniqueness, square-integrable Langlands classification, square-integrable
exhaustion, or regular exhaustion. In particular, the local occurrence
is upgraded by the already published cuspidal constituent theorem and concrete
adjointness, with no disjoint-support decomposition or classification input.
