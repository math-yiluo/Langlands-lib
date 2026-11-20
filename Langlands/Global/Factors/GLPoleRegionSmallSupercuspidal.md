# The GL pole region with a supercuspidal second member

This internal module supports the proof `Langlands.Global.glPairPoleRegion` of
`Langlands.Global.GLPairPoleRegionStatement`. It proves the case of Henniart (1986),
Proposition 4.5(ii), `GL_n` side, in which the second JPSS member `σ` is
supercuspidal and the first member `π` is generic. The ranks are arbitrary. The
statement needs this in unequal rank, where `σ` has the smaller rank. Henniart's
§4.8 (printed p.163) settles this case by "the same reasoning as in 4.7", the
juxtaposition argument of §4.7 (printed pp.161–162): a common zero makes two
Zelevinsky segments of `π` juxtaposed. The formal proof follows that argument.
Everything is over the canonical realization
`Fr = F.canonicalTopologicalData`, with residue cardinality `q > 1`.

## Segment combinatorics

Namespace `Langlands.Global.GLPoleRegion`, for segments of any realization. A
segment `Δ` has base `Δ.base`, length `Δ.length`, members
`Δ.member i = Δ.base ⊗ |det|^i` and last member `Δ.last`.

- `member_eq_of_base_eq_last_twist_one`: if `Γ.base = Δ.last ⊗ |det|`, then
  `Γ.member i = Δ.member (Δ.length + i)`.
- `isLinked_of_base_eq_last_twist_one`: such `Δ` and `Γ` are linked in the sense
  of the published `Segment.IsLinked` (Zelevinsky 1980, §4.1).
  - Neither support contains the other. The first member `Δ.member 0` of `Δ`
    is not a member `Δ.member (Δ.length + i)` of `Γ`, and the first member
    `Δ.member Δ.length` of `Γ` is not a member `Δ.member i`, `i < Δ.length`, of
    `Δ`, because `i ↦ Δ.member i` is injective on `ℕ`
    (`segment_member_injective`).
  - Their union is the support of the segment with base `Δ.base` and length
    `Δ.length + Γ.length`.

  This is the statement "juxtaposed segments are linked".
- `base_ne_last_twist_one Δ`: a segment cannot begin at the unit twist of its own
  end, that is, `Δ.base ≠ Δ.last ⊗ |det|`. Otherwise
  `Δ.member 0 = Δ.member Δ.length`, against injectivity. (Other segments may
  begin there.)

## Poles at `s = 0` against a supercuspidal representation

- `castRank_castRank` and `nonempty_equiv_cast_of_iso` are bookkeeping for the
  published rank transport `castRank`.
- `exists_last_eq_dualDatum_of_eval_one_eq_zero` has the following data:
  - `π` the Langlands quotient of a precedence-ordered segment-head datum `d` on
    `GL_(n+1)(F)` (`SegmentProductDatum.IsLanglandsQuotient`);
  - `A` a supercuspidal representation of `GL_(t+1)(F)`, representing the
    cuspidal datum `c`;
  - `P` an L-polynomial of `π × A` in the sense of the published
    `IsLanglandsPairLPolynomial`, with `P(1) = 0`.

  It concludes that some segment `Δ_i` of `d` ends at the dual datum `c^∨`.
  1. The published `orderedSegmentSquareIntegrableConversion` turns `d` into a
     square-integrable Langlands datum `e`, with an index permutation that
     matches segment heads to blocks.
  2. `A` is the segment head of the one-element segment `D` of `c`
     (`HighlyRamified.singletonSegment_isSegmentHead`). It is essentially square
     integrable (`exists_isEssentiallySquareIntegrable_equiv_of_isSegmentHead`).
  3. The published pole-order formula `lPolynomialPoleOrderAtZero_eq_poleLinkCount`
     applies. Its inputs are the closed theorems `squareIntegrableDataLFactor`,
     `segmentHeadLFactor`, `supercuspidalEqualRankLFactor` and
     `supercuspidalUnequalRankLFactor`. The Whittaker type of supercuspidal
     representations comes from `supercuspidalKirillov`. The formula gives
     the multiplicity of the root `1` of `P` as
     `poleLinkCount {Δ_1, …, Δ_r} D^∨`.
  4. The root is present, so this count is positive. Some `Δ_k` therefore
     satisfies `SegmentPoleLink Δ_k D^∨`, which includes `Δ_k.last ∈ D^∨.support`.
     Since `D^∨` has one member `c^∨`, this gives `Δ_k.last = c^∨`.
- `isLanglandsPairLPolynomial_of_isPadicSymmetricLPolynomial`: for generic `π` and
  `σ`, a symmetric p-adic pair L-polynomial is also an `IsLanglandsPairLPolynomial`.
  The published `langlandsPairLFactorExistence` gives some `Q` with that
  relation. `IsLanglandsPairLPolynomial.isPadicSymmetricLPolynomial` and
  uniqueness give `Q = P`.
- `exists_unlinked_isLanglandsQuotient_dual`: a generic `π` of `GL_(r+1)(F)` (a
  bundled smooth representation) has the following datum `d`:
  - `d` is a segment-head product with pairwise unlinked segments, by the
    published Zelevinsky Theorem 9.7 exhaustion `genericSegmentProductExhaustion`;
  - `π` is the Langlands quotient of `d`, since unlinked data are
    precedence-ordered;
  - the smooth contragredient `π^∨` is the Langlands quotient of the dual datum
    `d.dual`. This uses `UnlinkedSocleProduct.isLinked_of_dual`,
    `SegmentProductDatum.contragredientInducedIso` and `isGeneric_contragredient`.

## Main theorem

`hasNoReflectedCommonZero_of_supercuspidal_right ν hπ hiσ hscσ hP hPd` has the
following hypotheses:

- `π` on `GL_(r+1)(F)` generic for `ψ`;
- `σ` on `GL_(t+1)(F)` irreducible and supercuspidal;
- `P` the symmetric p-adic L-polynomial of `π × σ` at a self-dual `ν`;
- `Pd` that of the smooth contragredients `π^∨ × σ^∨`, for the same `ψ` and `ν`.

It concludes `HasNoReflectedCommonZero q P Pd`. Suppose `z ≠ 0` satisfies
`P(z) = 0` and `Pd(q⁻¹z⁻¹) = 0`.

1. `π` is moved to the carrier universe `max uF uV` (`SmoothRep.universeLift`).
   `exists_unlinked_isLanglandsQuotient_dual` gives `d`.
2. Choose `u` with `q^(-u) = z` (`HighlyRamified.exists_spectralPoint_eq`). Put
   `ρ = σ ⊗ |det|^u`. It is irreducible and supercuspidal (`isIrreducible_twist_iff`,
   `isSupercuspidal_twist_iff`). It has a realization `A` in the universe
   `max uF uV` (`padicIrreducibleSmoothSmallRealization`). By
   `Padic.symmetricLPolynomial_determinantComplexPower`, the polynomial
   `P(q^(-u) X)` is the L-polynomial of `π × A`. It vanishes at `1`. The previous
   section gives a segment `Δ_i` of `d` with `Δ_i.last = c^∨`, where `c` is the
   cuspidal datum of `A`.
3. Likewise `Pd(q^(-(1-u)) X)` is the L-polynomial of `π^∨ × σ^∨ ⊗ |det|^(1-u)`.
   The second member is equivalent to `A' = twistedDualRep 1 A`, which represents
   `c^∨ ⊗ |det|` (`twistedDualRep_represents`). The equivalence uses
   `smoothContragredientTwistEquiv` and the character identity
   `|det|^1 · |det|^(-u) = |det|^(1-u)`. At `X = 1` this polynomial is
   `Pd(q⁻¹ z⁻¹) = 0` (`spectralPoint_one_sub`). The previous section, applied to
   `π^∨` and `d.dual`, gives `j` with `(Δ_j^∨).last = (c^∨ ⊗ |det|)^∨`.
4. Dualizing (`Segment.dual_last`, `dualDatum_dualDatum`, `dualDatum_twist`) gives
   `Δ_j.base = c^∨ ⊗ |det| = Δ_i.last ⊗ |det|`. So the base of `Δ_j` represents
   `(σ ⊗ |det|^u)^∨ ⊗ |det| = σ^∨ ⊗ |det|^(1-u)`, the unit twist of the end of
   `Δ_i`.
   - If `i = j`, this contradicts `base_ne_last_twist_one`.
   - If `i ≠ j`, then `Δ_i` and `Δ_j` are linked by
     `isLinked_of_base_eq_last_twist_one`. This contradicts unlinkedness of `d`.

For `i ≠ j`, step 4 is Henniart's exclusion of juxtaposed components in §4.7.
Henniart's text does not separate the case `i = j`. The explicit check that a
segment is not adjacent to itself (`base_ne_last_twist_one`, by injectivity of
segment members) is the formal proof's own.

## The form used by the statement

`hasNoReflectedCommonZero_of_supercuspidal_le ν htr hπ hiσ hscσ hP hPd` has the
following hypotheses:

- `t ≤ r`;
- `P` the p-adic pair L-polynomial of `(π, σ)` for `ψ` at `ν`;
- `Pd` that of `(π^ι, σ^ι)` for `ψ.scale (-1)` at `ν`.

These are the forms produced by `isPadicPairLPolynomial_of_unequalRank`. It
reduces to the main theorem as follows:

1. Both relations are symmetric relations (`isPadicSymmetricLPolynomial_of_le`).
2. The dual relation is changed to the character
   `(ψ.scale (-1)).scale (-1) = ψ` (`IsPadicSymmetricLPolynomial.characterChange`,
   `UnitaryAdditiveCharacter.scale_scale`).
3. `π^ι`, `σ^ι` are replaced by the smooth contragredients. This is the published
   Gelfand–Kazhdan transport
   `isPadicSymmetricLPolynomial_inverseTranspose_iff_smoothContragredient`.

## Dependencies

The module imports `Langlands.Global.Factors.GLPoleRegionSupercuspidal` (this
submission) and the published modules listed in its header: segment
classification (`SegmentTensorStabilizerProof`,
`UnlinkedSocleProductIrreducibilityProof`,
`OrderedSegmentSquareIntegrableConversionProof`,
`GenericSegmentProductExhaustionProof`, `SegmentHeadProductContragredient`), the
pole-order and L-factor theorems (`SquareIntegrablePoleOrderCharacterizationReduction`,
`SquareIntegrableDataLFactorProof`, `SegmentHeadFactorProof`,
`SupercuspidalEqualRankLFactorProof`, `LanglandsPairLFactorExistenceProof`), and
`HighlyRamified/PairInductionGenericity`, `HighlyRamified/ShellExpansion`,
`AdjacentRankClearingKernel` and `Correspondence/AutomorphicActualGamma`. It
introduces no axioms and no hypotheses.
