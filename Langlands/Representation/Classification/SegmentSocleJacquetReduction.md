# Conditional reduction of the two-block Jacquet formula for segment socles

The generic helpers in this module are also imported by
[`SegmentHeadJacquetReduction`](SegmentHeadJacquetReduction.md), which retains
the separate head-specific formulas. Both reductions use the same helper
declarations in `Langlands.Classification.SegmentSocleJacquetReduction`.

Author: Worker 756.

This module reduces the published proposition
`Langlands.Classification.SegmentSocleJacquetFormula` from
[`SegmentSocleJacquetStatement`](SegmentSocleJacquetStatement.md) (Zelevinsky 1980,
Proposition 3.4) to four published propositions, H1–H4 below. **It does not prove
the target proposition, and it proves none of H1–H4.** The unconditional theorem
`Langlands.Classification.segmentSocleJacquetFormula` in
[`SegmentSocleJacquetProof`](SegmentSocleJacquetProof.md) applies
`segmentSocleJacquetFormula_of` to the published proofs of H1–H4. The field universe
`uF` and the representation universe `uV` are independent throughout, as in the
target.

## Hypotheses

Fix a prime `p` with `[Fact p.Prime]`, `F : PadicField.{uF} p` and
`T : F.TopologicalData`. All four hypotheses are taken for this one `F` and `T`.

- **H1** `Classification.SegmentSubrepresentationFullJacquet.{uF, uV} F T` from
  [`SegmentFullJacquetStatement`](SegmentFullJacquetStatement.md) (Zelevinsky 1980,
  3.1). For every segment `Δ`, every supercuspidal representative `A` of
  `Δ.base` and every `π` with `T.IsSegmentSubrepresentation Δ π`, the normalized
  Jacquet module of `π` along the uniform shape `(r, …, r)` is equivalent to the
  external tensor product of `T.segmentFactors A.obj Δ.length Δ.rank_pos`, that is,
  of `A, νA, …, ν^(m-1) A`.
- **H2** `CuspidalSupport.NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n`
  for every `n`, from
  [`JacquetInductionStatement`](../CuspidalSupport/JacquetInductionStatement.md)
  (Bernstein–Zelevinsky 1977, Corollary 2.13(b)). If `ρ` is quasicuspidal on the
  Levi of `B` and the Levis of `B` and `C` are not associated, then every
  quasicuspidal subquotient of the normalized Jacquet module along `C` of the
  normalized induction of `ρ` from `B` is zero.
- **H3** `Classification.SegmentZelevinskyConstituentExistence.{uF, uV} F T` from
  [`SegmentConstituentStatement`](SegmentConstituentStatement.md). Every segment `Δ`
  has a representation `π` with `T.IsSegmentSocle Δ π` that is moreover, for every
  supercuspidal representative `A` of `Δ.base`, the irreducible head of the
  decreasing-order induction `T.segmentInducedDown A.obj m _`. Only the socle part is
  used.
- **H4** `CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n` for every
  `n`, from
  [`NormalizedCuspidalInductionStatement`](../CuspidalSupport/NormalizedCuspidalInductionStatement.md)
  (Bernstein–Zelevinsky 1977, Theorem 2.8). Normalized induction of an irreducible
  cuspidal representation of a block Levi has finite length. Only finite length is
  used, not the bound on the composition length.

## Declarations

All declarations are in namespace
`Langlands.Classification.SegmentSocleJacquetReduction`. Below, `m = Δ.length`,
`r = Δ.rank` and `n = Δ.degree = m * r`. The representation
`π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)` and the Jacquet
functors are those of the target.

**Block combinatorics.**

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
  refinements of the same shape, whose blocks (flattened blocks) all have the same
  positive size `r` are equal.

**General representation theory.**

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
- `nontrivial_of_isIrreducible ρ h`: an irreducible representation has a nontrivial
  carrier.

**Refined Jacquet modules.**

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
  (`MinimalJacquet.flattenJacquetMap_surjective`). The comparison isomorphism is not
  used.
- `exists_refinement_size_eq hr hH2` (**Lemma K**). Assume H2 in rank `m * r`. Let
  `ρ` be quasicuspidal on the Levi of `BlockShape.uniform m r hr`, and let `π` embed
  in the normalized induction of `ρ` from that shape. Let `C : BlockShape (m * r)`,
  let `P ⟶ (T.normalizedJacquetFunctor C).obj π` be injective and `P ⟶ X` be
  surjective, with `X` nontrivial. Then some `S : BlockRefinement C` has all blocks
  of `C.flatten S` of size `r` and a nontrivial refined Jacquet module
  `RefinedJacquetModule C S X.representation`.

**Segments.**

- `segmentInduced_eq T A m hr`: `T.segmentInduced A m hr` is, by definition, the
  normalized induction from `BlockShape.uniform m r hr` of the external tensor
  product of `T.segmentFactors A m hr`.
- `segmentFactors_isLeviQuasicuspidal T m hm hr A`: for `0 < m` and a supercuspidal
  `A`, that external tensor product is quasicuspidal.
- `jacquet_ofPair_subsingleton T hH2` (**clause 1**). Assume H2 in every rank. For
  every `Δ`, every `π` with `T.IsSegmentSubrepresentation Δ π` and every
  `0 < l < n` with `¬ r ∣ l`, the normalized Jacquet module of `π` along
  `BlockShape.ofPair l (n - l) …` is `Subsingleton`. This is the first clause of the
  target, for all irreducible subrepresentations of the segment induction, not only
  for its socle.
- `uniformRefinement hr C len hlen`: the refinement of a shape whose blocks have
  sizes `len j * r` into blocks of size `r`.
- `twistIsoOfEq` and `segmentFactorTwistIso T A s t u h`: twists by equal characters
  are isomorphic, and `ν^s (ν^t A) ≅ ν^u A` when `u = s + t`.
- `nonempty_productInduced_iso_uniform`: normalized product induction from a shape
  `B` equal to `BlockShape.uniform k r hr` of factors `σ` is isomorphic to the one
  from the uniform shape of factors `τ` when corresponding factors are isomorphic.
  The factors are compared through `HEq` because their groups are only
  propositionally equal.
- `nonempty_segmentInduced_iso_socleSplit T Δ q hq hqm A` (**induction in
  stages**). For `0 < q < m` and every smooth `A` of `GL_r`, the segment induction
  `T.segmentInduced A m _` is isomorphic to the normalized product induction from
  `Δ.socleSplitShape q hq hqm` of the factors `T.segmentInduced A q _` and
  `T.segmentInduced (T.segmentFactor A q) (m - q) _`.
- `twistRep T s A`: the twist `ν^s A` of a supercuspidal representative, and
  `terminal_isRepresentedBy_twistRep`: if `A` represents `Δ.base`, then `ν^q A`
  represents the base of `Δ.terminal q hqm`.
- `exists_socleSplit_embedding T Δ q hq hqm A hA π₁ π₂ h₁ h₂`: if `A` represents
  `Δ.base`, `π₁` is a socle of `Δ.initial q hq` and `π₂` a socle of
  `Δ.terminal q hqm`, then the normalized product induction from
  `Δ.socleSplitShape q hq hqm` of `Δ.socleSplitFactors q hq hqm π₁ π₂` has an
  injective intertwiner into `T.segmentInduced A.obj m _`.

**Clause 2.**

- `jacquet_map_injective T hr hH2`. Assume H2 in rank `m * r`. Let `ρ` be
  quasicuspidal on the uniform Levi, let `π` embed in the normalized induction of
  `ρ` from the uniform shape, and let the normalized Jacquet module of `π` along
  every shape equal to the uniform shape be irreducible. Then every surjection
  `φ : (T.normalizedJacquetFunctor C).obj π ⟶ X` onto a nontrivial `X` is
  injective.
- `isIrreducible_isAdmissible_of_isSegmentSocle`: a segment socle is irreducible and
  admissible.
- `isIrreducible_socleSplitTensor`: the external tensor product of a socle of the
  initial segment and a socle of the terminal segment is irreducible.
- `segmentInduced_finiteLength T hH4 Δ A`: assuming H4, the segment induction of a
  supercuspidal `A` has finite length over `MonoidAlgebra ℂ (GeneralLinear n F.Carrier)`.
- `isIrreducible_jacquet_uniform T hH1 Δ A π hA hπ`: assuming H1, the normalized
  Jacquet module of a segment subrepresentation along every shape equal to the
  uniform shape is irreducible.
- `nonempty_socleSplit_jacquet_iso T hH1 hH2 hH4` (**clause 2**). Assume H1, and H2
  and H4 in every rank. For every `Δ`, every `π` with `T.IsSegmentSocle Δ π`, every
  `0 < q < m` and **all** `π₁`, `π₂` with `T.IsSegmentSocle (Δ.initial q hq) π₁` and
  `T.IsSegmentSocle (Δ.terminal q hqm) π₂`, there is an isomorphism
  `(T.normalizedJacquetFunctor (Δ.socleSplitShape q hq hqm)).obj π ≅
  FiniteTensor.externalFunctor.obj (Δ.socleSplitFactors q hq hqm π₁ π₂)`.

**Assembly.**

- `segmentSocleJacquetFormula_of T hH1 hH2 hH3 hH4`: H1, H2 in every rank, H3 and
  H4 in every rank imply `Classification.SegmentSocleJacquetFormula.{uF, uV} F T`.

## Implemented proof

Let `A` be a supercuspidal representative of `Δ.base`, let
`ρ_Δ` be the external tensor product of `A, νA, …, ν^(m-1) A`, and let
`I = T.segmentInduced A.obj m _`, the normalized induction of `ρ_Δ` from the uniform
shape. `ρ_Δ` is irreducible and cuspidal by the published
`segmentFactors_isIrreducible_isLeviCuspidal`, hence quasicuspidal.

1. **Lemma K.** The published `minimalNonzeroRefinedJacquet` gives a refinement `S`
   of `C` such that the refined Jacquet module of `X` along `S` is nonzero and, on
   the Levi of `C.flatten S`, quasicuspidal. Then
   `flattenedRefinedJacquet T C S X` is a subquotient of the normalized Jacquet
   module along `C.flatten S` of `I`: pull the injection obtained from `P ⟶ r_C(π)`
   back along the surjection `flattenedQuotient T C S π`
   (`exists_injective_surjective_of_pullback`), compose with the Jacquet functor
   applied to `π ↪ I`, which is injective
   (`JacquetDetectingFamilyLengthProof.jacquet_injective`), and with the surjection
   induced by `P ⟶ X`. If the uniform shape and `C.flatten S` were not associated,
   H2 would make this nonzero subquotient zero. So they are associated, and
   `size_eq_of_levisAssociated_uniform` (via the published
   `TotalConjugatingCount.blockMap_surjective` and `size_blockMap`) gives block size
   `r`.
2. **Clause 1.** Suppose the Jacquet module along `C = (l, n - l)` is nonzero. Lemma
   K with `P = X` equal to it gives a refinement `S` into blocks of size `r`, so
   `l = (S 0).length * r` and `r ∣ l`.
3. **Induction in stages.** With `S = uniformRefinement` of the split
   `(q r, (m - q) r)` into blocks of size `r`, the published
   `Parabolic.orderedProductRegrouping` regroups the product induction from
   `C.flatten S`, which equals the uniform shape, into the product induction from `C`
   of two product inductions. The factors are matched blockwise: the flattened index
   of `(0, k)` is `k` and that of `(1, k)` is `q + k` (`finSigmaFinEquiv_apply`), and
   `ν^k (ν^q A) ≅ ν^(q+k) A` (`segmentFactorTwistIso`).
4. **The embedding.** By `isSegmentSocle_iff`, with the representatives `A` and
   `ν^q A`, the socles `π₁` and `π₂` embed into the segment inductions of the initial
   and terminal segments. The published
   `normalizedProduct_embedding_of_factor_embeddings` and step 3 give an injection
   `W ↪ I`, where `W` is the normalized product induction of `π₁, π₂` from the split.
5. **Lifting the socle.** `W` is nonzero (the published
   `RegularHeadExistence.nontrivial_normalizedProductInduction`), and `I` has finite
   length by H4. So `exists_mem_range_of_isIrreducibleSocle` puts the image of the
   socle embedding `π ↪ I` inside the image of `W`, using an atom of the
   subrepresentation lattice below the image of `W`. `exists_lift_of_mem_range` lifts
   it to a nonzero intertwiner `ψ : π → W`.
6. **Frobenius reciprocity.** The published bijection
   `Parabolic.FirstAdjointness.equiv` turns `ψ` into a nonzero intertwiner
   `φ : r_C(π) → π₁ ⊠ π₂`. The target is irreducible: `π₁` and `π₂` are irreducible
   and admissible (`segmentInductionAdmissibility`, `isAdmissible_of_injective`), so
   Schur's lemma `admissibleSchur` holds for both and the published
   `FiniteTensor.isIrreducible_external` applies. Hence `φ` is surjective.
7. **Injectivity.** By H1 the Jacquet module of `π` along the uniform shape is
   equivalent to `ρ_Δ`, hence irreducible (`isIrreducible_iff_of_equiv`). In
   `jacquet_map_injective`, suppose `ker φ ≠ 0`. Lemma K, applied to `ker φ` and to
   `X`, gives refinements `S` and `S'` into blocks of size `r`. They are equal
   (`refinement_eq_of_size_eq`), and `C.flatten S` is the uniform shape. The
   composite of `flattenedQuotient` with the map induced by `φ` is a nonzero
   surjection out of the irreducible Jacquet module along the uniform shape, so it is
   injective. A nonzero element of the refined Jacquet module of `ker φ` maps to a
   nonzero element `z` of the refined Jacquet module of `r_C(π)`, which the map
   induced by `φ` kills. Lifting `z` through `flattenedQuotient` gives an element of
   the kernel of that injective composite, so `z = 0`, a contradiction.
8. **Assembly.** `φ` is bijective, which gives the isomorphism
   (`SmoothRep.mkIso`). H3 supplies the socles `π₁` and `π₂` of the initial and
   terminal segments required by the existential second clause of the target.

All objects are the actual ones of the target: actual normalized Jacquet functors,
actual normalized parabolic induction and the actual external tensor functor. No
Jacquet module, socle or isomorphism is taken as data.

## Relation to the source route

The source proof of 3.4 (printed pp.181–182) identifies the two-block Jacquet module
as an irreducible `σ₁ ⊗ σ₂` by computing the Jacquet module of an external tensor
product (its 1.5(a)) and then recognizes `σ₁` and `σ₂` by 3.1 for the shorter
segments. The Lean proof avoids 1.5(a) and this recognition. It maps the Jacquet
module onto the given `π₁ ⊠ π₂` by Frobenius reciprocity (steps 4–6) and proves
injectivity from H1 and H2 (step 7). For clause 1 it uses BZ77 2.13(b) (H2) through
Lemma K, where the source cites 2.13(a) or 1.6.

## Provenance

Internal. These are supporting lemmas for
[`SegmentSocleJacquetProof`](SegmentSocleJacquetProof.md); the main lemma
`segmentSocleJacquetFormula_of` is an implication between published Library
propositions, and no source statement is translated. The route follows Zelevinsky 1980, Proposition 3.4,
printed pp.181–182 (source `zelevinsky-1980-induced-ii`), as described above. The
hypotheses are the Library's statements of Zelevinsky 1980, 3.1 (H1, H3),
Bernstein–Zelevinsky 1977, Corollary 2.13(b) (H2, source
`bernstein-zelevinsky-1977-induced-i`), and Bernstein–Zelevinsky 1977, Theorem 2.8
(H4).
