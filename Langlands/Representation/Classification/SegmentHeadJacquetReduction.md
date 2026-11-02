# Conditional reduction of the two-block Jacquet formula for segment heads

Authors: Worker 256 and Worker 756.

This module reduces the published proposition
`Langlands.Classification.SegmentHeadJacquetFormula` from
[`SegmentHeadJacquetStatement`](SegmentHeadJacquetStatement.md) (Zelevinsky 1980,
Proposition 9.5) to four published propositions, H1′, H2, H3′ and H4 below. **It does
not prove the target proposition, and it proves none of H1′, H2, H3′ and H4.** The
field universe `uF` and the representation universe `uV` are independent throughout,
as in the target.

The generic lemmas (block combinatorics, pullbacks, socle lifting, refined Jacquet
modules, Lemma K, `jacquet_map_injective`, twist isomorphisms, `uniformRefinement`,
`nonempty_productInduced_iso_uniform`, `twistRep`, `terminal_isRepresentedBy_twistRep`
and `nontrivial_of_isIrreducible`) are Worker 756's and are imported from
[`SegmentSocleJacquetReduction`](SegmentSocleJacquetReduction.md), the socle-side
analogue for Ze80 3.4. They retain the
`Langlands.Classification.SegmentSocleJacquetReduction` namespace and one shared
implementation. Worker 756 approved this reuse. The head-side declarations are
new or adapted to the decreasing induction:
`nonempty_equiv_of_ker_eq`, `nonempty_iso_of_isSegmentHead`, `segmentInducedDown_eq`,
`segmentFactorsDown_isLeviQuasicuspidal`, `jacquet_ofPair_subsingleton`,
`nonempty_segmentInducedDown_iso_split`, `exists_split_embedding`,
`isIrreducible_isAdmissible_of_isIrreducibleSocle`, `isIrreducible_splitTensor`,
`segmentInducedDown_finiteLength`, `isIrreducible_jacquet_uniform`,
`nonempty_split_jacquet_iso`, `segmentHeadJacquetFormula_of` and the clause.

## Hypotheses

Fix a prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`. All four hypotheses are taken for this one `F` and `T`.

- **H1′** `Classification.SegmentQuotientFullJacquet.{uF, uV} F T` from
  [`SegmentFullJacquetStatement`](SegmentFullJacquetStatement.md) (Zelevinsky 1980,
  9.1(*)). For every segment `Δ`, every supercuspidal representative `A` of
  `Δ.base` and every `π` with `T.IsSegmentQuotient Δ π`, the normalized Jacquet
  module of `π` along the uniform shape `(r, …, r)` is equivalent to the external
  tensor product of `T.segmentFactorsDown A.obj Δ.length Δ.rank_pos`, that is, of
  `ν^(m-1) A, …, νA, A`.
- **H2** `CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n`
  for every `n`, from
  [`JacquetInductionStatement`](../CuspidalSupport/JacquetInductionStatement.md)
  (Bernstein–Zelevinsky 1977, Corollary 2.13(b)). If `ρ` is quasicuspidal on the
  Levi of `B` and the Levis of `B` and `C` are not associated, then every
  quasicuspidal subquotient of the normalized Jacquet module along `C` of the
  normalized induction of `ρ` from `B` is zero.
- **H3′** `Classification.SegmentSpecialConstituentExistence.{uF, uV} F T` from
  [`SegmentConstituentStatement`](SegmentConstituentStatement.md) (Zelevinsky 1980,
  9.1). Every segment `Δ` has a representation `π` with `T.IsSegmentHead Δ π` that
  is moreover, for every supercuspidal representative `A` of `Δ.base`, the
  irreducible socle of the decreasing-order induction
  `T.segmentInducedDown A.obj m _`.
- **H4** `CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n` for every
  `n`, from
  [`NormalizedCuspidalInductionStatement`](../CuspidalSupport/NormalizedCuspidalInductionStatement.md)
  (Bernstein–Zelevinsky 1977, Theorem 2.8). Normalized induction of an irreducible
  cuspidal representation of a block Levi has finite length. Only finite length is
  used, not the bound on the composition length.

## Declarations

The head-specific declarations are in namespace
`Langlands.Classification.SegmentHeadJacquetReduction`. The shared declarations
attributed below to Worker 756 are imported from
`Langlands.Classification.SegmentSocleJacquetReduction`. Below, `m = Δ.length`,
`r = Δ.rank` and `n = Δ.degree = m * r`. The representation
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)` and the Jacquet
functors are those of the target.

**Block combinatorics** (Worker 756).

- `size_eq_of_levisAssociated_uniform hr h j`: if `D : BlockShape (m * r)` is
  `LevisAssociated` with `BlockShape.uniform m r hr`, then every block of `D` has
  size `r`.
- `refinement_size_eq S h i j`: if all blocks of `C.flatten S` have size `r`, so do
  all blocks of every `S i`.
- `eq_length_mul_of_size_eq D h`: a shape of `k` whose blocks all have size `r`
  satisfies `k = D.length * r`.
- `eq_uniform_of_size_eq hr D h`: a shape of `q * r` whose blocks all have size `r`
  equals `BlockShape.uniform q r hr`.
- `blockShape_eq_of_size_eq` and `refinement_eq_of_size_eq`: two shapes, or two
  refinements of the same shape, whose (flattened) blocks all have the same positive
  size `r` are equal.

**General representation theory** (Worker 756, except `nonempty_equiv_of_ker_eq`).

- `exists_injective_surjective_of_pullback f hf i hi`: for smooth representations of
  a topological group over a field, a surjection `f : Z ⟶ R` and an injection
  `i : Y ⟶ R`, there are `K`, an injection `K ⟶ Z` and a surjection `K ⟶ Y`. Here
  `K` is the preimage under `f` of the range of `i`.
- `compMap φ f` and `compMap_apply`: an intertwiner stays an intertwiner after both
  actions are pulled back along a monoid homomorphism `φ`.
- `exists_lift_of_mem_range ι hι j h`: an intertwiner `j` whose values lie in the
  range of an injective intertwiner `ι` factors as `ι ∘ ψ`.
- `exists_mem_range_of_isIrreducibleSocle hs hfin hX ι hι`: let
  `Classification.IsIrreducibleSocle ρ π` hold, let `ρ` have finite length over
  `MonoidAlgebra ℂ G`, and let `ι : σ → ρ` be injective with nontrivial source. Then
  there is an injective `j : π → ρ` with all values in the range of `ι`.
- `nonempty_equiv_of_ker_eq q hq q' hq' h`: two surjective intertwiners `q`, `q'`
  out of the same representation with equal linear kernels have equivalent targets.
  The equivalence is `quotKerEquivOfSurjective` composed with `quotEquivOfEq`.
- `nontrivial_of_isIrreducible ρ h`: an irreducible representation has a nontrivial
  carrier.

**Refined Jacquet modules** (Worker 756).

- `flattenedRefinedJacquet T C S X`: the normalized refined Jacquet module
  `T.normalizedRefinedJacquet C S X.representation`, pulled back to the Levi of
  `C.flatten S` along `flattenedLeviEquiv F.Carrier C S`, as a smooth
  representation. `flattenedRefinedJacquetMap T C S f` is the induced map, which is
  injective for injective `f` (`flattenedRefinedJacquetMap_injective`, from
  `RefinedJacquetLengthProof.map_injective`) and surjective for surjective `f`
  (`flattenedRefinedJacquetMap_surjective`).
- `flattenedQuotient T C S π`: the published `Parabolic.flattenedJacquetQuotientMap`
  from `(T.normalizedJacquetFunctor (C.flatten S)).obj π` to
  `flattenedRefinedJacquet T C S ((T.normalizedJacquetFunctor C).obj π)`, as a
  morphism. `flattenedQuotient_surjective` says it is surjective
  (`MinimalJacquet.flattenJacquetMap_surjective`).
- `exists_refinement_size_eq hr hH2` (**Lemma K**). Assume H2 in rank `m * r`. Let
  `ρ` be quasicuspidal on the Levi of `BlockShape.uniform m r hr`, and let `π` embed
  in the normalized induction of `ρ` from that shape. Let `C : BlockShape (m * r)`,
  let `P ⟶ (T.normalizedJacquetFunctor C).obj π` be injective and `P ⟶ X` be
  surjective, with `X` nontrivial. Then some `S : BlockRefinement C` has all blocks
  of `C.flatten S` of size `r` and a nontrivial refined Jacquet module
  `RefinedJacquetModule C S X.representation`.

**Segments.**

- `nonempty_iso_of_isSegmentHead T Δ π π' h h'`: two representations `π`, `π'` with
  `T.IsSegmentHead Δ π` and `T.IsSegmentHead Δ π'` are isomorphic. Unfold `h` to a
  representative `A`, a surjection `q` from `T.segmentInduced A.obj m _` onto `π` and
  the kernel-uniqueness clause of `IsIrreducibleHead`. `isSegmentHead_iff` gives a
  surjection `q'` onto `π'` from the same induction, with `π'` irreducible. The
  uniqueness clause gives `ker q' = ker q`, and `nonempty_equiv_of_ker_eq` applies.
- `segmentInducedDown_eq T A m hr`: `T.segmentInducedDown A m hr` is, by definition,
  the normalized induction from `BlockShape.uniform m r hr` of the external tensor
  product of `T.segmentFactorsDown A m hr`.
- `segmentFactorsDown_isLeviQuasicuspidal T m hm hr A`: for `0 < m` and a
  supercuspidal `A`, that external tensor product is quasicuspidal (from the
  published `Classification.segmentFactorsDown_isIrreducible_isLeviCuspidal`).
- `jacquet_ofPair_subsingleton T hH2` (**clause 1**). Assume H2 in every rank. For
  every `Δ`, every representative `A`, every `π` with an injective intertwiner into
  `T.segmentInducedDown A.obj m _` and every `0 < l < n` with `¬ r ∣ l`, the
  normalized Jacquet module of `π` along `BlockShape.ofPair (n - l) l …` is
  `Subsingleton`.
- `uniformRefinement hr C len hlen` (Worker 756): the refinement of a shape whose
  blocks have sizes `len j * r` into blocks of size `r`.
- `twistIsoOfEq` and `segmentFactorTwistIso T A s t u h` (Worker 756): twists by equal
  characters are isomorphic, and `ν^s (ν^t A) ≅ ν^u A` when `u = s + t`.
- `nonempty_productInduced_iso_uniform` (Worker 756): normalized product induction
  from a shape `B` equal to `BlockShape.uniform k r hr` of factors `σ` is isomorphic
  to the one from the uniform shape of factors `τ` when corresponding factors are
  isomorphic. The factors are compared through `HEq` because their groups are only
  propositionally equal.
- `nonempty_segmentInducedDown_iso_split T Δ q hq hqm A` (**induction in stages**).
  For `0 < q < m` and every smooth `A` of `GL_r`, the decreasing segment induction
  `T.segmentInducedDown A m _` is isomorphic to the normalized product induction from
  `Δ.splitShape q hq hqm` (block sizes `((m - q) r, q r)`) of the factors
  `T.segmentInducedDown (ν^q A) (m - q) _` (first block) and
  `T.segmentInducedDown A q _` (second block).
- `twistRep T s A` and `terminal_isRepresentedBy_twistRep` (Worker 756): the twist
  `ν^s A` of a supercuspidal representative, and if `A` represents `Δ.base`, then
  `ν^q A` represents the base of `Δ.terminal q hqm`.
- `exists_split_embedding T Δ q hq hqm A π₁ π₂ h₁ h₂`: if `π₁` is the irreducible
  socle of `T.segmentInducedDown (ν^q A) (m - q) _` and `π₂` that of
  `T.segmentInducedDown A q _`, then the normalized product induction from
  `Δ.splitShape q hq hqm` of `Δ.splitFactors q hq hqm π₁ π₂` has an injective
  intertwiner into `T.segmentInducedDown A.obj m _`.

**Clause 2.**

- `jacquet_map_injective T hr hH2` (Worker 756). Assume H2 in rank `m * r`. Let `ρ`
  be quasicuspidal on the uniform Levi, let `π` embed in the normalized induction of
  `ρ` from the uniform shape, and let the normalized Jacquet module of `π` along
  every shape equal to the uniform shape be irreducible. Then every surjection
  `φ : (T.normalizedJacquetFunctor C).obj π ⟶ X` onto a nontrivial `X` is
  injective.
- `isIrreducible_isAdmissible_of_isIrreducibleSocle`: the irreducible socle of a
  decreasing segment induction is irreducible and admissible.
- `isIrreducible_splitTensor`: the external tensor product of irreducible admissible
  `π₁` and `π₂` on the two blocks of the split is irreducible.
- `segmentInducedDown_finiteLength T hH4 Δ A`: assuming H4, the decreasing segment
  induction of a supercuspidal `A` has finite length over
  `MonoidAlgebra ℂ (GeneralLinear n F.Carrier)`.
- `isIrreducible_jacquet_uniform T hH1 Δ A π hA hπ`: assuming H1′, the normalized
  Jacquet module of a segment quotient `π` along every shape equal to the uniform
  shape is irreducible.
- `nonempty_split_jacquet_iso T hH1 hH2 hH4` (**clause 2 for the embedded head**).
  Assume H1′, and H2 and H4 in every rank. Let `A` represent `Δ.base`, and let `π`
  satisfy `T.IsSegmentQuotient Δ π` and be the irreducible socle of
  `T.segmentInducedDown A.obj m _`. For every `0 < q < m` and **all** `π₁`, `π₂`
  that are the irreducible socles of `T.segmentInducedDown (ν^q A) (m - q) _` and
  `T.segmentInducedDown A q _`, there is an isomorphism
  `(T.normalizedJacquetFunctor (Δ.splitShape q hq hqm)).obj π ≅
  FiniteTensor.externalFunctor.obj (Δ.splitFactors q hq hqm π₁ π₂)`.

**Assembly.**

- `segmentHeadJacquetFormula_of T hH1 hH2 hH3 hH4`: H1′, H2 in every rank, H3′ and
  H4 in every rank imply `Classification.SegmentHeadJacquetFormula.{uF, uV} F T`.
- `SegmentHeadJacquetReductionClause` is a proposition (`Prop`) with universe
  parameters `uF` and `uV`: for every prime `p` with `[Fact p.Prime]`, every
  `F : PadicField.{uF} p` and every `T : F.TopologicalData`, H1′, `∀ n`, H2, H3′ and
  `∀ n`, H4 for `F` and `T` imply `SegmentHeadJacquetFormula.{uF, uV} F T`.
- `segmentHeadJacquetReductionClause_holds` proves this clause.

## Implemented proof

Let `π` satisfy `T.IsSegmentHead Δ π`, and let `A` be the representative it contains.
Let `ρ_Δ` be the external tensor product of `ν^(m-1) A, …, νA, A` and let
`I = T.segmentInducedDown A.obj m _`, the normalized induction of `ρ_Δ` from the
uniform shape. `ρ_Δ` is irreducible and cuspidal by the published
`segmentFactorsDown_isIrreducible_isLeviCuspidal`, hence quasicuspidal.

1. **Reduction to an embedded head.** H3′ gives `π₀` with `T.IsSegmentHead Δ π₀` that
   is the irreducible socle of `I`. By `nonempty_iso_of_isSegmentHead`, `π₀ ≅ π`.
   Applying the Jacquet functors to this isomorphism transfers both clauses from
   `π₀` to `π`. So it suffices to treat `π₀`, which is both a segment quotient
   (`IsSegmentHead.isSegmentQuotient`) and a subrepresentation of `I`.
2. **Lemma K.** The published `minimalNonzeroRefinedJacquet` gives a refinement `S`
   of `C` such that the refined Jacquet module of `X` along `S` is nonzero and, on
   the Levi of `C.flatten S`, quasicuspidal. Then `flattenedRefinedJacquet T C S X`
   is a subquotient of the normalized Jacquet module of `I` along `C.flatten S`.
   Pull the injection obtained from `P ⟶ r_C(π)` back along the surjection
   `flattenedQuotient T C S π` (`exists_injective_surjective_of_pullback`), compose
   with the Jacquet functor applied to `π ↪ I`, which is injective
   (`JacquetDetectingFamilyLengthProof.jacquet_injective`), and with the surjection
   induced by `P ⟶ X`. If the uniform shape and `C.flatten S` were not associated,
   H2 would make this nonzero subquotient zero. So they are associated, and
   `size_eq_of_levisAssociated_uniform` (via the published
   `TotalConjugatingCount.blockMap_surjective` and `size_blockMap`) gives block size
   `r`.
3. **Clause 1.** Suppose the Jacquet module of `π₀` along `C = (n - l, l)` is
   nonzero. Lemma K with `P = X` equal to it gives a refinement `S` into blocks of
   size `r`, so `l = (S 1).length * r` and `r ∣ l`.
4. **Induction in stages.** With `S = uniformRefinement` of the split
   `((m - q) r, q r)` into blocks of size `r`, the published
   `Parabolic.orderedProductRegrouping` regroups the product induction from
   `C.flatten S`, which equals the uniform shape, into the product induction from `C`
   of two product inductions. The factors are matched blockwise. The flattened index
   of `(0, k)` is `k` and that of `(1, k)` is `(m - q) + k` (`finSigmaFinEquiv_apply`).
   The decreasing factor at flattened index `t` is `ν^(m-1-t) A`. For `k < m - q`,
   `ν^(m-1-k) A ≅ ν^(m-q-1-k) (ν^q A)` (`segmentFactorTwistIso`), and
   `ν^(m-1-(m-q+k)) A = ν^(q-1-k) A`.
5. **The embedding.** H3′ for `Δ.terminal q hqm` and `Δ.initial q hq` gives heads
   `π₁` and `π₂` that are the irreducible socles of the decreasing inductions of the
   representatives `ν^q A` (`terminal_isRepresentedBy_twistRep`) and `A`. The
   published `normalizedProduct_embedding_of_factor_embeddings` and step 4 give an
   injection `W ↪ I`, where `W` is the normalized product induction of `π₁, π₂` from
   the split.
6. **Lifting the socle.** `W` is nonzero (the published
   `RegularHeadExistence.nontrivial_normalizedProductInduction`), and `I` has finite
   length by H4. So `exists_mem_range_of_isIrreducibleSocle` puts the image of the
   socle embedding `π₀ ↪ I` inside the image of `W`, using an atom of the
   subrepresentation lattice below the image of `W`. `exists_lift_of_mem_range` lifts
   it to a nonzero intertwiner `ψ : π₀ → W`.
7. **Frobenius reciprocity.** The published bijection
   `Parabolic.FirstAdjointness.equiv` turns `ψ` into a nonzero intertwiner
   `φ : r_C(π₀) → π₁ ⊠ π₂`. The target is irreducible: `π₁` and `π₂` are irreducible
   and admissible (`segmentInductionAdmissibility`, `isAdmissible_of_injective`), so
   Schur's lemma `admissibleSchur` holds for both and the published
   `FiniteTensor.isIrreducible_external` applies. Hence `φ` is surjective.
8. **Injectivity.** By H1′, applied to the segment quotient `π₀`, the Jacquet module
   of `π₀` along the uniform shape is equivalent to `ρ_Δ`, hence irreducible
   (`isIrreducible_iff_of_equiv`). In `jacquet_map_injective`, suppose
   `ker φ ≠ 0`. Lemma K, applied to `ker φ` and to `X`, gives refinements `S` and
   `S'` into blocks of size `r`. They are equal (`refinement_eq_of_size_eq`), and
   `C.flatten S` is the uniform shape. The composite of `flattenedQuotient` with the
   map induced by `φ` is a nonzero surjection out of the irreducible Jacquet module
   along the uniform shape, so it is injective. A nonzero element of the refined
   Jacquet module of `ker φ` maps to a nonzero element `z` of the refined Jacquet
   module of `r_C(π₀)`, which the map induced by `φ` kills. Lifting `z` through
   `flattenedQuotient` gives an element of the kernel of that injective composite,
   so `z = 0`, a contradiction.
9. **Assembly.** `φ` is bijective, which gives the isomorphism (`SmoothRep.mkIso`).
   Composed with the Jacquet functor applied to `π ≅ π₀`, it gives the isomorphism
   of the second clause for `π`, with the heads `π₁` and `π₂` from step 5 as the
   required witnesses.

All objects are the actual ones of the target: actual normalized Jacquet functors,
actual normalized parabolic induction and the actual external tensor functor. No
Jacquet module, head or isomorphism is taken as data.

## Relation to the source route

Zelevinsky 1980, 9.5 (printed p.198) is proved by transferring the proof of 3.4
(printed pp.181–182) to the decreasing order. That proof identifies the two-block
Jacquet module as an irreducible `σ₁ ⊗ σ₂` by computing the Jacquet module of an
external tensor product (its 1.5(a)) and then recognizes `σ₁` and `σ₂` from their
full cuspidal Jacquet modules. The Lean proof avoids 1.5(a) and this recognition.
It realizes the head as the socle of the decreasing induction (H3′), maps its
Jacquet module onto the given `π₁ ⊠ π₂` by Frobenius reciprocity (steps 5–7), and
proves injectivity from H1′ and H2 (step 8). For clause 1 it uses BZ77 2.13(b) (H2)
through Lemma K, where the source cites 2.13(a) or 1.6. No derivative result
(Ze80 9.6 or BZ77 derivatives) is used.

## Dependency audit

The transitive `Langlands` import closure at Library commit
46ad94719738ee676dd6e863d6e924cca8fec970 has 257 modules. `lean_check` reports the
axioms `propext`, `Classical.choice` and `Quot.sound` only for
`segmentHeadJacquetReductionClause_holds`. Against the exclusions of task
55ad1e10-62d8-46b7-a081-909ef0056426:

- No module in the closure states or proves SegmentHeadProductIrreducibility,
  GenericSegmentProductUniqueness, multisegment exhaustion, ordered strong-head
  existence, quotient coverage, ordered conversion, tempered uniqueness,
  SquareIntegrableLanglandsClassification, square-integrable exhaustion,
  SegmentSpecialEssentialSquareIntegrability, analytic segment classification or
  `MultisegmentSocleExhaustion`. No derivative result occurs: the only closure
  module named `Derivative`, `Mirabolic`, `Whittaker` or `GelfandKazhdan` is
  `Whittaker.Iwasawa`, the Iwasawa decomposition of `GL_n`. A text search of the
  closure for the excluded names finds only `RegularLanglandsStatement` and
  `LanglandsData`, apart from this module.
- `RegularLanglandsStatement` enters through `RegularLanglandsHeadReduction`
  (Worker 156), imported for the unconditional lemma
  `RegularHeadExistence.nontrivial_normalizedProductInduction`. That statement
  module contains only the proposition definitions
  `GLRegularLanglandsHeadExistenceStatement`,
  `GLRegularLanglandsDataUniquenessStatement`, `GLRegularLanglandsExhaustionStatement`
  and `GLRegularLanglandsQuotientStatement`. None of them is assumed or used here.
  The lemma itself is proved from a compact local section with a nonzero tensor
  value and has no hypothesis beyond nonzero blocks.
- `LanglandsData` defines the data structure `SquareIntegrableLanglandsDatum`. It is
  not the classification statement or its proof.
- The four hypotheses are the only conditional inputs. They are published
  statements of Ze80 9.1(*), BZ77 2.13(b), Ze80 9.1 and BZ77 2.8, with proof tasks
  b331611c-526d-4925-87fe-ea67ed6e6fed, b17b8c8c-858b-4b48-994b-e3641cb05f02,
  67279e36-f3c2-42e3-9302-11729784042e and 7baa622d-e46d-4b7a-932d-2a33433ab201.
  This module neither imports nor depends on their proofs. Those proofs are
  published, and [`SegmentHeadJacquetProof`](SegmentHeadJacquetProof.md) supplies
  them. That module's Markdown audits their closures.

## Provenance

Internal. The clause is an implication between published Library propositions; no
source statement is translated. The route follows Zelevinsky 1980, Proposition 9.5,
printed p.198, with the proof of 3.4, printed pp.181–182 (source
`zelevinsky-1980-induced-ii`), as described above. The hypotheses are the Library's
statements of Zelevinsky 1980, 9.1(*) (H1′) and 9.1 (H3′),
Bernstein–Zelevinsky 1977, Corollary 2.13(b) (H2, source
`bernstein-zelevinsky-1977-induced-i`), and Bernstein–Zelevinsky 1977, Theorem 2.8
(H4). The generic lemmas come from Worker 756's socle-side reduction, as stated at
the top.
