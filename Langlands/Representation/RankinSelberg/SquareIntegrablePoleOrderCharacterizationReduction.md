# Henniart's Théorème 1.7(b) from its remaining prerequisites

Henniart 2002, Théorème 1.7(b), states the following. Let `π` and `π'` be
irreducible admissible representations of `GL_N(F)`, `N ≥ 2`, with `π` not
supercuspidal. Suppose that, for every irreducible essentially
square-integrable `ρ` of `GL_r(F)`, `1 ≤ r ≤ N - 1`, the factors
`L(s, π × ρ)` and `L(s, π' × ρ)` have poles of the same order at `s = 0`.
Then `π ≃ π'`. The Library states it as
`RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement`, with
`N = n + 2`, test ranks `r + 1` for `r ≤ n`, and the L-factors given by
`IsLanglandsPairLPolynomial`.

This module derives that statement from the prerequisites that the Library
states but does not yet prove. The main theorem is unconditional apart from
these prerequisites. It does not prove the statement outright.

## The prerequisites

`SquareIntegrablePoleOrderCharacterizationPrerequisites.{uF, uV, uW}` is the
conjunction of the following Library propositions:

- for every prime `p` and every `p`-adic field `F` in universe `uF`, with its
  canonical topological data, `Classification.SquareIntegrableLanglandsExhaustion`
  and `Classification.SquareIntegrableLanglandsClassification` in the universe
  pair `{uF, uV}` (Henniart 2002, §2.8: every irreducible representation is the
  Langlands head of an essentially square-integrable datum, and two such heads
  are isomorphic exactly when the blocks agree up to order and isomorphism);
- `SquareIntegrableDataLFactorStatement.{uF, uV, uW}`: JPSS 1983,
  Theorem (9.5), in the product form of Henniart 2002, §2.8;
- `SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV}`: Henniart 2002,
  §2.6, the L-factor of a pair of segment heads;
- `SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV}`: JPSS 1983,
  Proposition (8.1)(ii).

None of the four is proved in Library commit 6f182f92.

The accepted module `SquareIntegrableDataPoleOrder` also takes JPSS 1983,
Proposition (8.1)(i), and the Whittaker type of irreducible supercuspidal
representations as hypotheses. Both are proved in the Library, and the main
theorem here discharges them inside its proof. (8.1)(i) is
`RankinSelberg.supercuspidalUnequalRankLFactor`, in the universe triple
`{uF, max uF uV, max uF uV}`. The Whittaker type comes from
`Langlands.supercuspidalKirillov` in universe pair `{uF, max uF uV}` and
`RankinSelberg.isOfWhittakerType_of_supercuspidalKirillov`. The latter is
applied to the two fields of the property of an irreducible supercuspidal
object: irreducibility and supercuspidality.

## Provenance

Derived. The proof follows Henniart's own route.

- Henniart 2002, Théorème 1.7(b), printed page 591 (PDF page 5), is the
  conclusion. Henniart 2002, §4.1, printed page 598 (PDF page 12), proves
  part (a) and says that part (b) is proved in the same way.
- Henniart 2002, §4.2, printed page 599 (PDF page 13): the pole order at
  `s = 0` is a count over the segments. On the representation side this is the
  accepted module `SquareIntegrableDataPoleOrder`. It computes the pole order
  of `L(s, π × St(D))` as `poleLinkCount a D^∨`, where `a` is the multisegment
  of `π`. It uses JPSS 1983, Theorem (9.5), Henniart 2002, §2.6, and JPSS 1983,
  Proposition (8.1).
- Henniart 2002, §§4.2-4.4, printed pages 599-600 (PDF pages 13-14): these link
  counts determine the multisegment. This is the accepted Library theorem
  `multisegment_eq_of_poleLinkCount_eq` of `PoleOrderSegmentCombinatorics`.
- Henniart 2002, §2.8, printed page 596: the classification of irreducible
  representations by essentially square-integrable data. The accepted module
  `SegmentLabelledDatumComparison` (Worker 1702) turns equal multisegments into
  isomorphic representations.
- The degree lemma and the realization of the test representation are
  internal helpers.

## Contents (namespace `RankinSelberg`)

- `SquareIntegrablePoleOrderCharacterizationPrerequisites` (definition, the
  selected declaration of the candidate): the conjunction above. Exhaustion and
  classification are combined for each `p` and `F`, in that order.
- `degree_map_univ_of_isSegmentLabelling`: let `d` be an essentially
  square-integrable Langlands datum of `GL_n(F)` and `Δ` a segment labelling
  of `d` (`IsSegmentLabelling d Δ`). Then the multisegment
  `Finset.univ.val.map Δ` has degree `n`. Each `deg Δ_i` is the size of
  block `i`, and the block sizes of the shape of `d` sum to `n`
  (`d.shape.sum_eq`).
- `exists_isEssentiallySquareIntegrable_equiv_of_isSegmentHead`: let `D` be a
  segment with `deg D = m` and `σ` a segment head of `D`. Then some
  irreducible essentially square-integrable `ρ` of `GL_m(F)`, with carrier in
  universe `max uF uW`, is equivalent to `castRank` of `σ`. The proof
  substitutes `m`. The head `σ` is irreducible and, by the proved Library
  theorem `segmentEssentialSquareIntegrableClassification`, essentially
  square-integrable. `ρ` is a small realization of `σ`
  (`padicIrreducibleSmoothSmallRealization`). Essential square-integrability
  transfers along the equivalence (`isEssentiallySquareIntegrable_iff_of_equiv`).
- `squareIntegrablePoleOrderCharacterization_of_classification` (main theorem):
  assume, for every `p` and `F`, the exhaustion and the classification, and
  also (9.5), §2.6 and (8.1)(ii), in the universes listed above. Then
  `SquareIntegrablePoleOrderCharacterizationStatement.{uF, uV, uW}` holds.
- `squareIntegrablePoleOrderCharacterization_of_prerequisites`: the same
  conclusion from `SquareIntegrablePoleOrderCharacterizationPrerequisites`.

## Proof of the main theorem

Let `π` and `π'` of `GL_(n+2)(F)` be as in the statement, with `π` not
supercuspidal and the pole-order hypothesis `htest`.

1. The exhaustion gives essentially square-integrable data `d` and `d'`. Their
   Langlands heads are `π` and `π'`, so they present `π` and `π'` as
   irreducible quotients (`IsLanglandsHead.isLanglandsQuotient`).
2. `exists_isSegmentLabelling` gives segment labellings `Δ` of `d` and `Δ'`
   of `d'`. Let `a = Finset.univ.val.map Δ` and `a' = Finset.univ.val.map Δ'`.
   Both have degree `n + 2` by `degree_map_univ_of_isSegmentLabelling`.
3. `multisegment_eq_of_poleLinkCount_eq` with `N = n + 2` gives `a = a'`. It
   needs two inputs.
   - `a` is not a single segment of length one. Otherwise `π` would be
     supercuspidal by `isSupercuspidal_of_segmentLabelling_eq_singleton`.
   - For every segment `D` with `deg D < n + 2`, the link counts of `a` and
     `a'` at `D` agree. By the proved Library theorem
     `segmentSpecialConstituentExistence`, the contragredient segment `D^∨`
     (`Segment.dual`) has a segment head `σ`. Since `deg D^∨ = deg D ≥ 1`,
     the degree is `(deg D - 1) + 1`. The previous lemma gives an irreducible
     essentially square-integrable `ρ` of `GL_(deg D)(F)` equivalent to `σ`.
     It is a test representation of rank `r + 1` with `r = deg D - 1 ≤ n`.
     `htest` gives L-polynomials `P` and `P'` of `π × ρ` and `π' × ρ` with
     equal pole orders at `s = 0`. The main theorem of
     `SquareIntegrableDataPoleOrder`, `lPolynomialPoleOrderAtZero_eq_poleLinkCount`,
     identifies these pole orders with `poleLinkCount a (D^∨)^∨` and
     `poleLinkCount a' (D^∨)^∨`. Here `(D^∨)^∨ = D` (`Segment.dual_dual`).
4. `nonempty_iso_of_segmentLabelling_eq`, with the classification, turns
   `a = a'` into an isomorphism `π ≅ π'`. `SmoothRep.equivOfIso` makes it an
   equivalence of the underlying representations.

## Dependencies

All imports except two are in Library commit 6f182f92. The two exceptions are
accepted candidates that are not yet merged. The snapshot contains unchanged
copies of both.

- `Langlands/Representation/RankinSelberg/SquareIntegrableDataPoleOrder.lean`
  and `.md`: candidate 74b8d9c2 (Worker 1710).
- `Langlands/Representation/RankinSelberg/SegmentLabelledDatumComparison.lean`
  and `.md`: candidate a0bc4e01 (Worker 1702).
