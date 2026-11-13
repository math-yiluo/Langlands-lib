# Exact exhaustion from a tempered opposite-Jacquet untwist

Worker 148. This internal reduction isolates the remaining exponent-selection
obligation in the opposite-Jacquet route to Langlands exhaustion. It does not
assert that the selection obligation has been proved.

`OppositeJacquetUntwistSelectionStatement` requires, for every irreducible
ambient smooth representation and the fixed choices in the exact exhaustion
statement, an actual opposite standard Jacquet exponent and a `UnitaryUntwist`
for it. The untwist must be normalized-exponent tempered on its original
standard Levi, and the original exponent's real part must lie in the open
coroot chamber for its original standard index and component factor.
The statement assumes no quotient map.

`isLanglandsTriplet_untwist` uses the already verified original standard root
presentation for the compatibility clause. The record supplies irreducibility;
temperedness is the explicit premise. The positive unramified realization has
exactly the actual exponent's real part, so the chamber premise gives the final
clause of `IsLanglandsTriplet`.

`langlandsQuotientExhaustive_of_selectedUnitaryUntwist` proves exactly
`LanglandsQuotientExhaustiveStatement` from this closed selection proposition
and the closed `LeviSecondAdjointnessStatement`. It applies selection with the
original fixed torus, generic cocharacter, reflection data and minimal
parabolic. The original standard parabolic datum and split component supply
all existential witnesses. The preceding triplet theorem supplies the
Langlands conditions, while `exists_surjective_standardInduction_untwist`
supplies the actual surjective intertwiner onto the original irreducible
ambient representation.

All constructions retain independent field universe `u` and original carrier
universe `v`. The provenance is internal assembly of the published standard
presentation, actual real-parameter realization and unitary-untwist interfaces.
Neither input proposition is proved here. In particular, the substantive
maximal-exponent argument yielding a tempered untwist in the open chamber
remains to be proved; this conditional reduction does not prove the
unconditional classification.
