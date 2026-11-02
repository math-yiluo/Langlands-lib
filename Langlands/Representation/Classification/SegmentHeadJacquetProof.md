# Two-block Jacquet modules of special segment heads (Zelevinsky 1980, Proposition 9.5)

Authors: Worker 256 and Worker 756.

## Declaration

- `Langlands.Classification.segmentHeadJacquetFormula`: for a prime `p` with
  `[Fact p.Prime]`, `F : PadicField.{uF} p` and `T : F.TopologicalData`, it proves
  `Classification.SegmentHeadJacquetFormula.{uF, uV} F T` from
  [`SegmentHeadJacquetStatement`](SegmentHeadJacquetStatement.md). The field universe
  `uF` and the representation universe `uV` are independent, as in the statement. The
  theorem has no hypotheses beyond the telescope
  `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.

The statement is Zelevinsky 1980, Proposition 9.5, for proper splits. Let `Δ` have
length `m`, cuspidal rank `r` and degree `n = m r`, and let `π` satisfy
`T.IsSegmentHead Δ π`. Then:

1. for `0 < l < n` with `¬ r ∣ l`, the normalized Jacquet module of `π` along
   `BlockShape.ofPair (n - l) l …` is a subsingleton;
2. for `0 < q < m`, there are `π₁` with `T.IsSegmentHead (Δ.terminal q _) π₁` and
   `π₂` with `T.IsSegmentHead (Δ.initial q _) π₂`, and an isomorphism of smooth
   representations
   `(T.normalizedJacquetFunctor (Δ.splitShape q _ _)).obj π ≅
   FiniteTensor.externalFunctor.obj (Δ.splitFactors q _ _ π₁ π₂)`.

## Proof

The theorem applies
`SegmentHeadJacquetReduction.segmentHeadJacquetFormula_of T hH1 hH2 hH3 hH4` from the
supporting module [`SegmentHeadJacquetReduction`](SegmentHeadJacquetReduction.md),
which derives the target from four published propositions. Each one is supplied by a
published, premise-free theorem of the Library for the same `F` and `T`:

- **H1′** `SegmentQuotientFullJacquet.{uF, uV} F T` (Zelevinsky 1980, 9.1(*), for
  segment quotients). It is the second conjunct `.2` of
  `Classification.segmentFullJacquetFormula.{uF, uV} F T`
  ([`SegmentFullJacquetProof`](SegmentFullJacquetProof.md)), which proves
  `SegmentFullJacquetFormula = SegmentSubrepresentationFullJacquet ∧
  SegmentQuotientFullJacquet`.
- **H2** `CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n` for
  every `n` (Bernstein–Zelevinsky 1977, Corollary 2.13(b)), from
  `CuspidalSupport.nonassociatedJacquetSubquotients F T n`
  ([`NonassociatedJacquetSubquotientsProof`](../CuspidalSupport/NonassociatedJacquetSubquotientsProof.md)).
- **H3′** `SegmentSpecialConstituentExistence.{uF, uV} F T` (Zelevinsky 1980, 9.1:
  each segment has a head that is the irreducible socle of the decreasing segment
  induction), from `Classification.segmentSpecialConstituentExistence F T`
  ([`SegmentSpecialConstituentExistenceProof`](SegmentSpecialConstituentExistenceProof.md)).
  This is the published result of task 67279e36-f3c2-42e3-9302-11729784042e, which
  the contract requires reusing.
- **H4** `CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n` for every
  `n` (Bernstein–Zelevinsky 1977, Theorem 2.8), from
  `CuspidalSupport.cuspidalInductionLength F T n`
  ([`NormalizedCuspidalInductionLengthProof`](../CuspidalSupport/NormalizedCuspidalInductionLengthProof.md)).
  Only the finite length of normalized cuspidal induction is used.

The mathematical argument is in the reduction module, under "Implemented proof". In
outline:

1. H3′ gives a head `π₀` of `Δ` that is the irreducible socle of the decreasing
   induction `I = T.segmentInducedDown A.obj m _`. By uniqueness of the irreducible
   head of the increasing induction (equal kernels), `π₀ ≅ π`. So it suffices to
   treat `π₀`, which is a segment quotient and a subrepresentation of `I`.
2. **Clause 1.** If the Jacquet module of `π₀` along `(n - l, l)` is nonzero, a
   minimal nonzero refined Jacquet module of it is a quasicuspidal subquotient of a
   Jacquet module of `I`. H2 forces its Levi to be associated with the uniform shape
   `(r, …, r)`, so all its blocks have size `r` and `r ∣ l`.
3. **Clause 2.** H3′ for `Δ.terminal q _` and `Δ.initial q _` gives heads `π₁` and
   `π₂` that are the socles of the shorter decreasing inductions. Induction in stages
   embeds the product induction `W` of `π₁, π₂` from `Δ.splitShape q _ _` into `I`.
   Because `I` has finite length (H4), the socle `π₀ ↪ I` lands in `W`. Frobenius
   reciprocity turns `π₀ → W` into a nonzero map from the two-block Jacquet module of
   `π₀` onto the irreducible `π₁ ⊠ π₂`. That map is injective because, by H1′, the
   full cuspidal Jacquet module of `π₀` is the irreducible
   `ν^(m-1) A ⊗ … ⊗ νA ⊗ A`, and by H2 every nonzero subquotient of the two-block
   Jacquet module has nonzero cuspidal Jacquet module along the uniform shape.
   Composing with `π ≅ π₀` gives the isomorphism for `π`.

All objects are the actual ones of the statement: the normalized Jacquet functor,
normalized parabolic induction and the external tensor functor. No Jacquet module,
head or isomorphism is taken as data.

## Relation to the source proof

Zelevinsky 1980, 9.5 (printed p.198, PDF p.35 of `zelevinsky-1980-induced-ii`) is
proved by transferring the proof of 3.4 (printed pp.181–182) to segment heads. That
proof uses BZ77 2.13(a) or Ze80 1.6 for clause 1, and for clause 2 it computes the
two-block Jacquet module through 1.5(a) and recognizes the shorter heads by their full
cuspidal Jacquet modules. The implemented proof keeps the vanishing argument (via
BZ77 2.13(b)), the full cuspidal Jacquet module 9.1(*) and finite length. It replaces
1.5(a) and the recognition step by Frobenius reciprocity against the heads given by
H3′. The reduction module's "Relation to the source route" section has the details.

## Dependency audit

The audit is for the transitive `Langlands` import closure of this module at Library
commit 46ad94719738ee676dd6e863d6e924cca8fec970, together with the supporting module.
The closure has 1121 modules. `lean_check` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound` for `segmentHeadJacquetFormula`.

### Independence exclusions

- The excluded results are SegmentHeadProductIrreducibility,
  GenericSegmentProductUniqueness, multisegment exhaustion, ordered strong-head
  existence, quotient coverage, ordered conversion, tempered uniqueness,
  SquareIntegrableLanglandsClassification, square-integrable and regular exhaustion,
  SegmentSpecialEssentialSquareIntegrability, analytic segment classification and
  `MultisegmentSocleExhaustion`. A text search of every closure module, in module
  names and source text, for these names and for `RegularLanglands` finds matches only
  in the supporting module and `RegularLanglandsHeadReduction` (both through the
  import below) and in the following two modules.
  - `RegularLanglandsStatement` contains only the proposition definitions
    `GLRegularLanglandsHeadExistenceStatement`,
    `GLRegularLanglandsDataUniquenessStatement`,
    `GLRegularLanglandsExhaustionStatement` and
    `GLRegularLanglandsQuotientStatement`. None of them is assumed or proved here.
    It enters through `RegularLanglandsHeadReduction`, which the reduction module
    imports only for the unconditional lemma
    `RegularHeadExistence.nontrivial_normalizedProductInduction`.
  - `LanglandsData` defines the data structure `SquareIntegrableLanglandsDatum`. It
    is not the classification statement or its proof.
- The closure has no module named after multisegment classification or exhaustion,
  strong heads, segment-product irreducibility, coverage of quotients, ordered
  conversion or generic segment products. (The modules `MirabolicMixedOrbitCoverage*`
  and `CompactCoefficient.SelectedCoverage` concern orbits and compact coefficients,
  and `TwoSupercuspidalNonadjacentIrreducibilityProof` is part of Ze80 1.11.) The other closure modules whose names
  mention tempered, essential, square-integrable or analytic objects are
  `Classification.Essential`, `Classification.Tempered`,
  `TemperedInductionStatement`, `TemperedSupportStatement`,
  `Unitary.SquareIntegrable{Statement,Proof}` and `RankinSelberg.AnalyticStatement`.
  They contain basic definitions (essential unitarizability, temperedness,
  square-integrability mod center), elementary lemmas, and unrelated proposition
  definitions. None of them is one of the excluded results or is used as a premise.
- No closure module other than this module and the supporting module imports
  `SegmentHeadJacquetStatement`, directly or transitively. So no input depends on the
  target, and the closure contains no downstream consumer of it, such as tasks
  8364e73f, 15540667 or 040c5597.
- The closure contains `SegmentQuotientJacquetSingleBlock` (task a91c30bb, Workers
  485 and 964). It is reached through H1′
  (`SegmentFullJacquetEdgeData` → `SegmentEdgeFamilyHypotheses` →
  `SegmentEdgeFactorHypotheses`). It is the elementary one-block case, in which the
  Jacquet module along a one-block shape is the representation itself. It imports only
  `Segments`, `MinimalJacquetProof` and `RegroupingFactorEquivalences`, uses no
  proper-block Jacquet calculation, and is not among this task's exclusions.

### Derivative results

The contract says the proof "must not assume a derivative formula (Ze80 9.6, BZ77
derivative results) or the current parent irreducibility criterion to obtain the
Jacquet formula". No derivative statement is a hypothesis of this theorem or of the
reduction. Neither this module nor the reduction module contains a derivative.
SegmentSpecialConstituentExistenceProof (H3′), NonassociatedJacquetSubquotientsProof
(H2) and NormalizedCuspidalInductionLengthProof (H4) have no derivative module in
their closures.

Derivative theory enters the closure only through H1′. `segmentFullJacquetFormula`
uses Zelevinsky 1980, 1.11 (`twoSupercuspidalProductStructure`, for two supercuspidal
representations). Conjunct (a) of 1.11 is the published premise-free
`twoSupercuspidalNonadjacentProductIrreducible`, which proves BZ77 Theorem 4.2 with
Bernstein–Zelevinsky derivatives. All 158 closure modules named `Derivative`,
`Mirabolic`, `Whittaker` or `GelfandKazhdan` lie in the closure of
`TwoSupercuspidalNonadjacentIrreducibilityProof`. In the reduction module's closure,
the only module with such a name is `Whittaker.Iwasawa`, the Iwasawa decomposition,
which contains no derivative.

The same clause appears in the 1.11 task ab61f565 and in task b331611c (H1′). A
trusted operator decision for the 1.11 task (request
`a8463ee15d57588c8de10306748b2538`, correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca`, `sender_role: operator`) interprets it. The
clause forbids assuming derivative results without proof and any circular
dependency. It does not forbid a fully proved BZ77 derivative route, under three
conditions. The published Markdown of
[`TwoSupercuspidalProductStructureProof`](TwoSupercuspidalProductStructureProof.md)
and of `SegmentFullJacquetProof` audits this. That decision was made for the 1.11
task. Its conditions also hold for this closure:

1. only general BZ77 derivative theory occurs. A search of the closure finds no
   segment derivative statement (`SegmentSocleDerivatives`,
   `HighestDerivativeSupportShift` or any segment-named derivative), so Ze80 3.5 and
   9.6 are neither stated nor used;
2. every derivative result in the closure is a proved, accepted and published
   Library theorem, and it is used only inside the premise-free 1.11 proof;
3. the closure contains none of this task's Independence exclusions (see above).
   The decision's own list (ed48ae06, b95105c6, 55ad1e10, 92aea10f, 2ae5cbe5,
   8364e73f) was the 1.11 task's exclusion list, and the 1.11 closure contains none
   of them, as its Markdown records. This closure necessarily also contains
   ed48ae06's statement and b331611c's proof, which supply H1′. No segment-socle
   derivative statement (the segment-socle part of task 8e5b4563) is in the closure.
   Segment socles occur only as the predicate `IsSegmentSocle` and the propositions
   about it in `Segments`, `SegmentConstituentStatement`,
   `SegmentConstituentCompatibilityStatement` and `LanglandsData`.

There is no circularity, since these derivative modules are about cuspidal pairs and
do not import the target statement or any segment-head Jacquet result.

## Provenance

The target is the published Library statement `SegmentHeadJacquetFormula`
(Zelevinsky 1980, Proposition 9.5). The inputs are the published Library proofs of
Zelevinsky 1980, 9.1(*) (task b331611c, artifact f2c2886a) and 9.1 (task 67279e36),
and of Bernstein–Zelevinsky 1977, Corollary 2.13(b) and Theorem 2.8 (source
`bernstein-zelevinsky-1977-induced-i`). The reduction module is joint work: its
generic lemmas are Worker 756's, from their socle-side reduction (candidate
e749a00f), and they are reused with Worker 756's approval.
