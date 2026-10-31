# Reduction of the supported regular Weyl and cone comparison

Authors: Worker 960, with Worker 165 (fixed-relation helper and the
numerical comparison statement).

This module is a conditional reduction. By itself it does not prove
`Langlands.GLSupportedRegularWeylConeComparisonStatement` unconditionally.
The final theorem `Langlands.SupportedRegularWeylCone.reduction` derives
that proposition, at its eight universes, from tempered induction
preservation `Langlands.GLTemperedInductionPreservationStatement`, taken
as an explicit hypothesis for each side at `.{uF, uW1}` and `.{uF, uW2}`.
The entry module
[`SupportedRegularWeylConeComparisonProof`](SupportedRegularWeylConeComparisonProof.md)
discharges both hypotheses with the published theorem
`Langlands.glTemperedInductionPreservation`.

The persistence input is supplied directly by the published theorem
`Langlands.glInducedCuspidalExponentPersistence` from
`InducedCuspidalExponentPersistenceProof`, at `.{uF, uV1, uW1, uV2}` and
`.{uF, uV2, uW2, uV1}`. The helper `oneSided` retains its explicit
persistence hypothesis; `reduction` fills it with these proved instances.
They retain one actual geometric-filtration piece to establish both the
twisted equivalence and occurrence at zero for the same permutation.

The numerical input is supplied directly by the published theorem
`Langlands.Exponents.supportedRegularWeylParameterNumerics` from
`SupportedRegularWeylParameterNumericsProof`. Its weighted lifting clause uses
`Langlands.Exponents.diagonal_cone_of_weighted_block_cone` from the shared
`WeightedBlockCone` module. All other inputs are also published proofs used
directly. The route is internal
derived content: it implements the parameter comparison extracted from
Silberger 1978, Proposition 6.1, in the form fixed by the target statement
Markdown. The step that reconciles two one-sided permutations by
Cauchy–Schwarz is internal to this project and is not claimed from the
literature.

## Class-exponent helpers

`classExponent_of_injective` turns an injective intertwiner from an
irreducible admissible Levi representation into the opposite Jacquet module
into `IsOppositeJacquetClassExponent`. Its witness is the range
subrepresentation together with the inverse linear equivalence onto it.

`classExponent_of_surjective` moves a class exponent from a quotient back to
the source. The opposite Jacquet map of a surjective intertwiner is
surjective by `coinvariants_map_surjective` applied to
`Jacquet.restrictMap`. The witness is the preimage subrepresentation of the
given one, mapped onto it by the restricted opposite Jacquet map.

`classExponent_of_inducedQuotient` applies the first clause of the
published `Parabolic.normalizedSecondAdjointness`. A surjection from the
normalized induction of an irreducible admissible `τ` onto an irreducible
admissible `J` is nonzero because `J` is nontrivial. Its adjoint
`τ → oppositeJacquet J` is therefore nonzero, hence injective by
irreducibility of `τ`. The first helper then applies.

## One-sided comparison

`oneSided` takes one side `(B, S, ω, v, π, t)` and the fine data
`(B', S', ω', v', π', t')` of the other side. Both twisted standard modules
are assumed to surject onto the same irreducible `J`. Only the first side
needs unitarizability and irreducibility of `π`.

1. `fineAmbientQuotientTransport` (the other side) gives a surjection from
   the fine induction of `τ`, the other fine representation twisted by
   `nestedParameter B' S' v' t'`, onto `J`.
2. `J` is admissible by the third clause of `relativeCosocleAdmissibility`,
   using `IsLeviTempered.isAdmissible` for `π'`. Twisting preserves
   irreducibility and cuspidality by the published twist `iff` lemmas.
   So `τ` is a class exponent of `J`, and then of the first side's real
   twisted induction `RealTwistFamilies.induced T B π t`.
3. The persistence hypothesis gives one permutation `s` and one witness
   `hs` with the required twisted equivalence. It also gives occurrence of
   the same transport at the untwisted point.
4. `RealTwistFamilies.induced_zero`, `transported_apply`,
   `nestedParameter_zero` and `leviComplexPowerTwist_ofReal` rewrite that
   occurrence as an opposite-Jacquet class exponent of the untwisted
   induction of `π`, with complex parameter `-v + I·0`.
5. The untwisted induction is tempered. The tempered-induction hypothesis
   applies with a Haar measure on the Levi central quotient from
   `exists_isHaarMeasure_leviCentralQuotient`.
6. The published `glTemperedOppositeTwistCone` with imaginary part `0`
   yields `IsClosedPositiveRootCone (fun a => v (blockIndex C (s.symm a)))`.

## Final assembly

`cast_cuspidalData` carries irreducibility, cuspidality and unitarizability
along `h : C = C'`. It is used for `ωB_i = h_i ▸ ω_i`.

`reduction` supplies the published persistence and numerical theorems,
introduces all data of the target statement and applies
`oneSided` twice. Side 1 against side 2 gives `s`, `hs`, the twisted
equivalence and the first cone bound. Side 2 against side 1 gives `r`,
`hr` and `cone(V2 ∘ r⁻¹)`. Worker 165's
`SupportedRegularWeylComparison.fixedRelation_of_twistedEquiv` converts each
equivalence into a fixed relation, `V1 ∘ s⁻¹ - A1 ∘ s⁻¹ = V2 - A2` and
`V2 ∘ r⁻¹ - A2 ∘ r⁻¹ = V1 - A1`. The second clause of the published numerics
theorem, applied to each side's positive-root parameter and strictly
decreasing `t_i`, gives `cone(V_i)`, the orthogonality
`Σ V_i · A_i = 0` and antitonicity of `A_i`. Its third clause then gives
`IsClosedPositiveRootCone (fun a => V2 (s a))`. The witness is `w := s`.
All four conclusions of the target hold for this one `w`.
