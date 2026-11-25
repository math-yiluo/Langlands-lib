# Zelevinsky 1980, Proposition 4.6, step (1): the juxtaposed case, proof

This module has fourteen helper modules `Juxtaposed*`. The further supporting
modules written for this proof, which it imports, are listed in the dependency
audit below. Every other input is a published declaration imported by its Lean
name.

## Statement proved

```lean
theorem Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure.{uF,uV} F T`
of `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement`.
The statement pair and every pair it
imports are unchanged. The outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`. The
theorem has no further hypothesis and no theorem-valued premise. The universes
`uF` and `uV` are independent level parameters, and neither is saturated.

The proposition is Zelevinsky 1980, Proposition 4.6, for juxtaposed segments.
Take `n`, a datum `d : T.SegmentProductDatum.{uV,uF} n` with `d.length = 2` and
`d.HasSegmentSocles`, and write `Δ = d.segments 0`, `Δ' = d.segments 1` and
`π = d.induced`, Zelevinsky's `⟨Δ⟩ × ⟨Δ'⟩`. Assume that `Δ'` precedes `Δ` and
that `Δ'` is juxtaposed with `Δ`. The proposition then provides:

- a segment `U`, an optional segment `I` and a datum
  `e : T.SegmentProductDatum.{uV,uF} n` with
  `Δ.IsUnionIntersectionReplacement Δ' U I`, `List.ofFn e.segments = U :: I.toList`
  and `e.HasSegmentSocles`;
- irreducibility of `e.induced.representation`;
- a filtration `s : ObjectRepFiltration (Rep.of d.induced.representation) 2` with
  simple factors. Its graded piece 1 (`π/ω₀`) is equivalent to
  `e.induced.representation`, and its graded piece 0 (the subrepresentation `ω₀`)
  is not. Every irreducible subrepresentation of `π` equals
  `s.subrepresentation 1`.

The proof produces `I = none`, so `U = Δ ∪ Δ'` and `e` is the one-block datum
whose block is a segment socle of `U`.

## Implemented proof

The module contains one theorem:

```lean
theorem juxtaposedSegmentSocleReverseProductStructure ... :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T :=
  JuxtaposedShuffle.juxtaposedSegmentSocleReverseProductStructure_of_irreducible T
    (twoSegmentSocleShuffleJacquet F T)
    fun hr A a b hab => JuxtaposedShuffle.uniform_two_isIrreducible_of_nonadjacent T
      (twoSupercuspidalNonadjacentProductIrreducible F T) hr A a b hab
```

`juxtaposedSegmentSocleReverseProductStructure_of_irreducible` (module
`JuxtaposedConditionalAssembly`) derives the target from two hypotheses:

- `hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T`, the shuffle
  count of the Jacquet module of a product of two segment socles on one cuspidal
  line (Zelevinsky 1980, 1.6 and 3.1). This module supplies the published
  `twoSegmentSocleShuffleJacquet F T` (module
  `TwoSegmentSocleShuffleJacquetProof`). Lean fixes its third universe to
  `max uF uV`.
- `hirr`: for `0 < r`, a supercuspidal representation `A` of `GL_r` and natural
  numbers `b + 1 < a`, the product `ν^a A × ν^b A` along
  `BlockShape.uniform 2 r` is irreducible. This module supplies it as
  `uniform_two_isIrreducible_of_nonadjacent` (module
  `JuxtaposedNonadjacentPairIrreducible`) applied to the published Zelevinsky
  1.11(a), `twoSupercuspidalNonadjacentProductIrreducible F T`. That lemma checks
  that the two twists are not adjacent and moves the irreducibility from
  `Shahidi.twoBlocks r r` on `GL_(r+r)` to the uniform shape on `GL_(2r)` by a
  rank cast.

The conditional theorem supplies its other inputs with published proofs:
`CuspidalSupport.nonassociatedJacquetSubquotients` (BZ77 2.13(b)), clause 1 of
`segmentFullJacquetFormula` (Zelevinsky 3.1) and
`exists_juxtaposedUnionHead` (module `JuxtaposedUnionHead`). The last one is applied to
`segmentZelevinskyConstituentExistence` (Zelevinsky 3.1 and 3.4).

### Mathematical route

Write `ρ = Δ'.base`, of rank `r`, with a supercuspidal representative `A`.
Let `l = Δ'.length` and `q = Δ.length`, so that `Δ.base = ν^l ρ`. Let `C` be the
uniform shape `(r, …, r)` with `q + l` blocks and `J` the normalized Jacquet
functor along `C`. For a set `S ⊆ {0, …, q+l-1}` with `q` elements, the shuffle
tensor `τ_S` is `⊗ᵢ ν^(e_S(i)) A`. Its exponents run through `l, …, l+q-1` at the
positions of `S` and through `0, …, l-1` elsewhere, both in increasing order.
`S_id` gives the increasing exponents `0, 1, …, q+l-1`. `S₀` gives the exponents
of `Δ` followed by those of `Δ'`. The datum is first normalized to
`n = (q + l) r` with beginnings `ν^l ρ` and `ρ`.

1. *Shuffle count* (`hS1`). `J(π)` has a composition series of length
   `C(q+l, q)`. The multiplicity of an irreducible `τ` in it is the number of
   sets `S` with `τ_S ≃ τ`.
2. *Distinct shuffles* (`JuxtaposedShuffleDistinct`). If `τ_S ≃ τ_{S'}`, then
   `S = S'`. This uses the factorwise comparison of cuspidal tensors
   (`CuspidalSupport.nonempty_equiv_of_factor_actions`,
   `cuspidalDatum_eq_of_equiv`) and the injectivity of integral twists
   (`cuspidalDatum_integralTwist_injective`). So `J(π)` is multiplicity free.
3. *Initial embedding* (`JuxtaposedInitialEmbedding`). There is an embedding
   `π ↪ i_C(τ_{S₀})`. The two socles embed into their increasing inductions, the
   product of the embeddings is an embedding
   (`normalizedProduct_embedding_of_factor_embeddings`), and the published
   regrouping `Parabolic.orderedProductRegrouping` identifies the product of the
   two inductions with `i_C(τ_{S₀})`.
4. *Shuffle swaps* (`JuxtaposedShuffleCombinatorics`, `JuxtaposedSwapLifting`,
   `JuxtaposedShuffleInducedIso`, `JuxtaposedSwapFromLibrary`). For every
   `S ≠ S_id` there is an isomorphism `i_C(τ_S) ≅ i_C(τ_{S₀})`. One passes from
   `S₀` to `S` by adjacent transpositions, each exchanging two factors
   `ν^a A, ν^b A` with `b + 1 < a`. On two blocks, irreducibility of
   `ν^a A × ν^b A` (`hirr`) and the published `irreducibleTwoFactorProductSwap`
   give `ν^a A × ν^b A ≅ ν^b A × ν^a A`. The regrouping lifts this isomorphism to
   the uniform shape.
5. *Cover* (`JuxtaposedJacquetCover`). For `S ≠ S_id` and every nonzero
   subrepresentation `X` of `π`, there is a nonzero map `J(X) → τ_S`. Compose
   `X ↪ π ↪ i_C(τ_{S₀}) ≅ i_C(τ_S)` and apply Frobenius reciprocity
   (`CuspidalSupport.exists_ne_zero_normalizedJacquet_hom`). So `τ_S` lies in the
   Jordan–Hölder support of the image of `J(X)` in `J(π)`
   (`jordanHolderSubobjectSimpleMapDetection`).
6. *Positivity* (`JuxtaposedJacquetPositivity`). Every nonzero subquotient of `π`
   has a nonzero Jacquet module along `C`. It is a subquotient of `i_C(τ_{S₀})`,
   and `τ_{S₀}` is quasicuspidal (`glCuspidalTensor`). So
   `one_le_jacquetLength_of_isSubquotient` applies, with `minimalNonzeroJacquet`
   and `nonassociatedJacquetSubquotients`. A shape associated to the uniform
   shape is the uniform shape (`eq_uniform_of_levisAssociated`).
7. *Lattice* (`JuxtaposedJacquetImage`, `JuxtaposedSupportLattice`,
   `JuxtaposedUniqueProperSub`). The map from `X` to the image of `J(X)` in `J(π)`
   is strictly monotone (by 6) and preserves intersections. In the multiplicity
   free module `J(π)` the images are determined by their Jordan–Hölder supports
   (`multiplicityFreeSubmoduleLattice`, `equivJordanHolderMultiplicityTransport`).
   By 5, the support of every nonzero `X` contains every `τ_S` with `S ≠ S_id`.
   So any two subrepresentations of `π` other than `⊥` and `⊤` are equal
   (`eq_of_ne_bot_of_ne_top_induced`).
8. *Separation* (`JuxtaposedUnionSeparation`). Let `σ` be a representation with
   `J(σ) ≃ τ_{S_id}`. No nonzero subrepresentation `X` of `π` is equivalent to
   `σ`. Otherwise step 5 for `S₀ ≠ S_id` gives a nonzero map
   `τ_{S_id} → τ_{S₀}`, which is an equivalence by Schur's lemma, and
   then step 2 gives `S₀ = S_id`. For `σ = e.induced`, Zelevinsky 3.1 gives
   `J(e.induced) ≃ τ_{S_id}` (`nonempty_jacquet_single_equiv`).
9. *Union datum and head* (`exists_juxtaposedUnionHead`, module
   `JuxtaposedUnionHead`). For
   juxtaposed `Δ'` preceding `Δ`, it provides `U = Δ ∪ Δ'`, `I = none`, the
   one-block datum `e` with a segment socle and the first four clauses of the
   target. It also shows that every irreducible quotient `π/K` is equivalent to
   `e.induced`. Its proof uses `segmentZelevinskyConstituentExistence`.
10. *Assembly* (`exists_filtration_core`). By `hS1`, `π ≠ 0`. If `π` were
    irreducible, then `π = π/⊥` would be an irreducible quotient, equivalent to
    `e.induced` by 9, against 8 for `X = ⊤`. So there is a `K ≠ ⊥, ⊤`, unique by 7.
    Then `⊥ ⋖ K ⋖ ⊤`, and the two-step filtration `⊥ ⊂ K ⊂ π` has simple factors.
    Its graded piece 1, `π/K`, is irreducible, hence equivalent to `e.induced`
    by 9. Its graded piece 0, `K`, is not, by 8. An irreducible subrepresentation
    is neither `⊥` nor `⊤`, so it equals `K` by 7.

The Markdown file of each helper module describes its step in detail.

## Scope

The theorem keeps arbitrary primes, finite p-adic fields, the supplied compatible
topology `T`, the actual upper normalized product induction `d.induced` and the
actual normalized Jacquet modules. It allows repeated and equal segments in the
quantified data and uses the published definitions by Lean name. The
filtration, its subrepresentations and the `Representation.Equiv`s are actual
objects. The theorem adds no finite-length, derivative, homogeneity, genericity,
commutation, irreducibility or existence premise.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980),
  literature ID `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Proposition 4.6 and step (1) of its proof (printed pp. 185–186, PDF pages
  22–23); §4.1 for linked, juxtaposed and preceding segments (printed p. 184);
  §1.6 and §3.1 (printed pp. 171–172 and 180–181) for the Jacquet module of
  `⟨Δ⟩ × ⟨Δ'⟩`; Proposition 1.11(a) (printed p. 175).
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 2.13 and 2.14, literature ID
  `bernstein-zelevinsky-1977-induced-i`.

Zelevinsky's step (1) uses 1.6 and 3.1 to compute the irreducible constituents
of `π`. They are `ω(r₁)` and `ω(r₂)` for two orientations `r₁, r₂` in the sense of
his §2, and `ω(r₁) = ⟨Δ ∪ Δ'⟩`. His Proposition 2.10 then shows that `π` has the
unique irreducible submodule `ω₀ = ω(r₂)`. The Lean proof uses the same
Jacquet-module computation (`hS1`). In place of the appeal to §2 it gives the
direct multiplicity argument of steps 2–8: Frobenius reciprocity into the
shuffle inductions, multiplicity freeness and the lattice of Jacquet images.
Steps 4 and 9 use the irreducibility of non-adjacent products (Zelevinsky
1.11(a)) and the existence of `⟨U⟩` with its head (Zelevinsky 3.1 and 3.4).

## Use of Zelevinsky 1.11(a)

Step 4 uses the published Zelevinsky 1980, Proposition 1.11(a):
`Langlands.Classification.twoSupercuspidalNonadjacentProductIrreducible`
(module `Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`). Its
proof uses the Bernstein–Zelevinsky derivative theory. This proof imports the
theorem by name. Neither this module nor its helper modules state, construct or
prove anything about derivatives.

It is admissible here for the following reasons. The requirement not to use or
duplicate derivative work governs this proof's own argument and the Library's
derivative constructions. It does not exclude published results that were
proved through derivatives. This proof reuses the published proof of
Zelevinsky 3.1, and its module `SegmentFullJacquetProof` already imports
`TwoSupercuspidalProductStructureProof` and through it
`TwoSupercuspidalNonadjacentIrreducibilityProof`. So 1.11(a) adds no module to
the closure of this proof (verified below). Zelevinsky 1.11(a) is not among the
exclusions. The theorem is imported by name, this proof adds no derivative
construction or argument of its own, and the closure of 1.11(a) is part of the
audit below.

## Dependency audit

All counts and checks below refer to Library commit
`47b67c4eb87954cf163f3a88bb94b9cbae2edbf0`, which contains the published S1
proof `Classification.TwoSegmentSocleShuffleJacquetProof`, together with the
fifteen modules of this proof. Module names omit the prefix `Langlands.`.

### Direct inputs

The proof modules imported by this module or its fourteen helper modules, and
what the proof takes from each:

| Input (module) | Use |
| --- | --- |
| `twoSegmentSocleShuffleJacquet` (`Representation.Classification.TwoSegmentSocleShuffleJacquetProof`) | `hS1`, Zelevinsky 1.6 and 3.1 for two segment socles |
| `twoSupercuspidalNonadjacentProductIrreducible` (`Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`) | `hirr`, Zelevinsky 1.11(a) |
| `segmentFullJacquetFormula` (`Representation.Classification.SegmentFullJacquetProof`) | clause 1, Zelevinsky 3.1, for `J(e.induced)` |
| `segmentZelevinskyConstituentExistence` (`Representation.Classification.SegmentZelevinskyConstituentExistenceProof`) | existence of `⟨U⟩` with its socle and head, input of `exists_juxtaposedUnionHead` |
| `CuspidalSupport.nonassociatedJacquetSubquotients` (`Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof`) | BZ77 2.13(b), positivity (step 6) |
| `CuspidalSupport.minimalNonzeroJacquet` (`Representation.CuspidalSupport.MinimalJacquetProof`) | BZ77 2.14, positivity (step 6) |
| `CuspidalSupport.glCuspidalTensor` (`Representation.CuspidalSupport.CuspidalTensorProof`) | shuffle tensors are irreducible and quasicuspidal |
| `CuspidalSupport.glCuspidalTensorAssociation` (`Representation.CuspidalSupport.CuspidalTensorAssociationProof`) | factorwise comparison of cuspidal tensors (step 2) |
| `segmentTensorStabilizerAndCuspidality` (`Representation.Classification.SegmentTensorStabilizerProof`) | `segmentSupercuspidalFactor`, injectivity of integral twists |
| `irreducibleTwoFactorProductSwap` (`Representation.Classification.IrreducibleTwoFactorProductSwapProof`) | two-block swap (step 4) |
| `Parabolic.orderedProductRegrouping` (`Representation.Parabolic.OrderedProductRegroupingProof`) | regrouping of products (steps 3 and 4) |
| `irreducibleProductEmbedding` (`Representation.Classification.IrreducibleProductEmbedding`) | its lemma `normalizedProduct_embedding_of_factor_embeddings` (step 3) |
| `jordanHolderSimpleMapDetection` (`Representation.Filtration.SimpleMapMultiplicityDetectionProof`) | its lemma `jordanHolderSubobjectSimpleMapDetection` (step 5) |
| `multiplicityFreeSubmoduleLattice` (`Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof`) | lattice of a multiplicity free module (step 7) |
| `multiplicityTransport` (`Representation.Filtration.MultiplicityTransportProof`) | its lemma `equivJordanHolderMultiplicityTransport` (step 7) |
| `LengthTwo.lengthTwoFactorMatchingCriterion` (`Representation.Filtration.LengthTwoMatching`) | its two-step filtration `LengthTwo.twoStep` with `twoStep_hasSimpleFactors`, and lattice lemmas (step 10) |

The helper modules also import the following Library modules, which are not
proof modules. `CuspidalSupport.InducedJacquetEvaluation` supplies
`exists_ne_zero_normalizedJacquet_hom` (step 5), and
`CuspidalSupport.InducedJacquetCount` supplies
`one_le_jacquetLength_of_isSubquotient` (step 6). Both are lemma modules of the
cuspidal-support development. The rest are definition modules:
`CuspidalSupport.JacquetLengthDetector`,
`CuspidalSupport.LeviAssociation`, `Induction.SingleBlock`,
`Filtration.ConstituentSupportDefinitions`,
`Classification.Segments` and
`Group.GL.AdjacentMergeShape`. The statement modules imported are
the target's, `TwoSegmentSocleShuffleJacquetStatement`,
`SegmentFullJacquetStatement` and
`TwoSupercuspidalProductStructureStatement`.

Supporting modules written for this proof and imported by it:

- `Representation.Classification.JuxtaposedUnionDatum`
- `Representation.Classification.JuxtaposedUnionHead`
- `Representation.Classification.SegmentSocleDecreasingHead`
- `Representation.Classification.JuxtaposedDecreasingQuotient`
- `Representation.Classification.JuxtaposedRefinementTools`

The closure of the S1 proof contains eight further supporting modules of the
same development: `TwoSourceShuffleLabels`, `UniformJacquetVanishing`,
`UniformRefinementCombinatorics`,
`UniformRefinementCoordinates`, `UniformRefinementLeviTransport`,
`UniformRefinementShuffleRealization`,
`UniformRefinementSurvivors` and `UniformTargetBlockLabels`. All thirteen of
these supporting modules in the closure are definition modules with finite
coordinates, segment data, transport, head and vanishing lemmas. None of them
states or assumes the target proposition.

### Import closure

A recursive scan of the `import` lines gives 1145 project modules in the
transitive closure, this module included. The closures of its four direct
imports have these sizes:

- `JuxtaposedConditionalAssembly`: 1130 modules. It contains the closure of
  `SegmentFullJacquetProof` (1038 modules), which contains the closure of
  Zelevinsky 1.11, `TwoSupercuspidalProductStructureProof` (879 modules).
- `TwoSegmentSocleShuffleJacquetProof`: 1055 modules. Thirteen of them lie
  outside the closure of `JuxtaposedConditionalAssembly`: the S1 proof module,
  its two supporting modules `TwoSegmentShuffleAssembly` and
  `TwoSegmentShufflePieces`, the eight further supporting modules listed above,
  `Geometric.WholeLeviPieceTransport` and
  `CuspidalSupport.QuasicuspidalJacquetVanishingProof`.
- `JuxtaposedNonadjacentPairIrreducible`: 297 modules.
- `TwoSupercuspidalNonadjacentIrreducibilityProof` (1.11(a)): 656 modules, all
  inside the closure of `SegmentFullJacquetProof`. So 1.11(a) adds no module.

Of the 1130 published modules in the closure, 273 are the entry modules of
proofs, 355 those of definitions or supporting modules and 241 those of
statements. The remaining 261 are helper modules of these, or early modules of
the Library.

### Exclusions

The checks below cover all the exclusions of this proof: the results listed
under *Declaration names* below, and
`LinkedSegmentSocleReverseProductQuotientHom` with any file proving it.

- *Modules of the excluded results.* The statement and proof modules of every
  excluded result were compared with the closure. None of them is in the
  closure. In particular, the proofs of ordered multisegment socle existence
  and of analytic segment classification are outside it. The only matches are
  seven definition modules introduced with socle exhaustion, explained below.
- *Proof modules.* None of the 273 proof modules of the closure (first
  inventory table below) proves an excluded result.
- *Declaration names.* The Lean files of the closure were searched for the
  excluded results: `LinkedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `LinkedSegmentSoclePairReducible`, `SegmentSocleProductIrreducibility`,
  `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
  `LinkedSegmentSocleGluing`, `OrderedMultisegmentSocleExistence`,
  `MultisegmentSocleExhaustion`,
  `SegmentEssentialSquareIntegrableClassification`,
  `MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
  `OrderedMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
  `SquareIntegrableLanglandsClassification`,
  `SquareIntegrableLanglandsExhaustion`, `GLRegularLanglandsExhaustion` and
  `SegmentHeadProductIrreducibility`. Only the target statement module
  `LinkedSegmentSocleReverseProductStepsStatement` contains any of them. It
  defines `LinkedSegmentSocleReverseProductQuotientHom` beside the target and
  names `LinkedSegmentSocleReverseProductStructure` in its documentation. No
  other module of the closure refers to
  `LinkedSegmentSocleReverseProductQuotientHom`, and it is not used. The
  optional inputs `UnlinkedSegmentSocleProductIrreducible` and
  `TwoFactorProductConstituentCommutativity` do not occur either.

Definition modules introduced with socle exhaustion:

- `Combinatorics.RelationInversions`,
  `Representation.Classification.SegmentIntegralCoordinates`,
  `Representation.Classification.SegmentIntervalLinkage` and
  `Representation.Classification.SegmentReplacementInversions`.
  The target statement module imports `SegmentReplacementInversions`, which
  defines `IsUnionIntersectionReplacement` and imports the other three directly
  or transitively. They are in the closure of the target statement itself, so no
  proof of it can avoid them.
- `Representation.Classification.SegmentUnionIntersection` and
  `Representation.Classification.SegmentProductReplacement`. They are the actual union/intersection segments and the
  segment-product replacement data. `JuxtaposedUnionDatum` uses them to build `U`
  and `e`.
- `Representation.Filtration.ObjectTransport`. It pulls an object
  filtration back along a monoid homomorphism and transports it along an
  equivalence. The closures of Zelevinsky 1.11 and 3.1 reach it through
  `NonadjacentSpecialization` and `OppositeCuspidalJacquetFiltrationProof`, and
  the S1 closure through `Tensor.ProductFiltration`.

These modules contain segment coordinates, interval combinatorics, inversion
counts, replacement data and filtration transport. None states, proves or
assumes `MultisegmentSocleExhaustion` or any other excluded result, and their
imports contain no excluded result. They are generic lower infrastructure, not
conclusions or proofs of an excluded result.

This proof does not import `Filtration.ObjectRepFiltrationTwoStep` or the
module it imports, `Filtration.FunctorLengthTwoDetection`. That abstract
lattice module was introduced with the excluded
`LinkedSegmentSocleReverseProductStructure`. The four facts needed here
(`quotientRepBotEquiv`, `topSubrepresentationEquiv`,
`subrepresentation_ne_bot_of_isIrreducible`, `eq_bot_or_eq_of_le_isIrreducible`)
are proved directly in `JuxtaposedConditionalAssembly`. So no module introduced
with `LinkedSegmentSocleReverseProductStructure` is in the closure.

There is no circularity. None of the closure modules imports this module, and
none assumes the target proposition.

### Derivative results

This module and its fourteen helper modules state, construct and prove nothing
about derivatives, and they use no derivative result directly. The closure
contains 158 modules whose names contain `Derivative`, `Mirabolic`,
`Whittaker` or `GelfandKazhdan`. All of them lie inside the closure (879
modules) of Zelevinsky 1.11, `twoSupercuspidalProductStructure` (module
`TwoSupercuspidalProductStructureProof`). It proves BZ77 Theorem 4.2 with the
published Bernstein–Zelevinsky derivative theory. The input
`SegmentFullJacquetProof` (Zelevinsky 3.1) imports it. The closure of 1.11(a),
the only result of that theory imported here directly, is a subset of the 1.11
closure. Among the helper modules' own lower inputs:

- `IrreducibleTwoFactorProductSwapProof` reaches
  `Smooth.Contragredient.GelfandKazhdanStatement`, `GelfandKazhdanProof` and
  `GelfandKazhdanAssembly`, the Gelfand–Kazhdan transpose involution;
- `JuxtaposedSwapLifting` and several other helpers reach
  `Whittaker.Iwasawa`, the Iwasawa decomposition of `GL_n`.

Neither is a derivative result. The closure contains no segment derivative
formula. A text search of its Lean files for `SegmentSocleDerivatives`,
`HighestDerivativeSupportShift`, `NonjuxtaposedSegmentSocleConstituentLevel`,
`SegmentHeadJacquetFormula` and `SegmentSocleJacquetFormula` finds nothing, and
no module of the closure belongs to the developments of Zelevinsky 3.5,
Zelevinsky 4.3, BZ77 4.7(b) or the segment socle derivative statements. The
derivative modules inside the 1.11 closure are published, and none of them is a
hypothesis of any step of this proof.

### Proved-module inventory

The first table lists every closure module that is the entry module of a
published proof (273 modules). None of them proves an excluded result.

| Proved module |
| --- |
| `Algebra.SandwichDimensionBoundProof` |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` |
| `Analysis.Local.QuotientAutomorphismProof` |
| `Analysis.Local.QuotientAveragingKernel` |
| `Analysis.Local.QuotientMeasureExistence` |
| `Analysis.Local.QuotientPositiveLifting` |
| `Galois.Local.AbsoluteProof` |
| `Group.GL.BlockContractionProof` |
| `Group.GL.BlockIwahoriBasis` |
| `Group.GL.BlockModulusHaarProof` |
| `Group.GL.BlockUnipotentHaarProof` |
| `Group.GL.CartanProof` |
| `Group.GL.CentralQuotientTopologyProof` |
| `Group.GL.CountabilityProof` |
| `Group.GL.InverseTransposeIwahoriProof` |
| `Group.GL.MirabolicMixedOrbitCoverageProof` |
| `Group.GL.MirabolicModularCharacterProof` |
| `Group.GL.MirabolicModulusProof` |
| `Group.GL.PrincipalBlockFactorizationProof` |
| `Group.GL.UpperBruhatBoundaryProof` |
| `Group.GL.UpperBruhatCoordinatesProof` |
| `Group.GL.UpperBruhatFiltrationGeometryProof` |
| `Group.GL.UpperBruhatLocalClosednessProof` |
| `Group.GL.UpperBruhatPivotProof` |
| `Group.GL.UpperBruhatProof` |
| `Group.GL.UpperBruhatRankProof` |
| `Group.GL.UpperBruhatTransposeProof` |
| `Group.GL.UpperUnipotentCompactContainmentProof` |
| `Group.GL.UpperUnipotentFactorizationProof` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionProof` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentProof` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityProof` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingProof` |
| `HarmonicAnalysis.Distribution.LocalizationProof` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof` |
| `HarmonicAnalysis.Distribution.TransposeInvariantProof` |
| `HarmonicAnalysis.PadicAdditiveConductorProof` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` |
| `HarmonicAnalysis.RowTensorDecompositionProof` |
| `HarmonicAnalysis.RowTestSmoothProof` |
| `HarmonicAnalysis.TriangularTranslationProof` |
| `LinearAlgebra.CyclicQuotientPairingProof` |
| `LinearAlgebra.MatrixAEvalConjugacyProof` |
| `LinearAlgebra.MatrixCharpolyConjugacyProof` |
| `LinearAlgebra.MatrixTransposeConjugateProof` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof` |
| `LocalField.SmoothCharacterNormProof` |
| `Representation.Category.ConstituentDichotomy` |
| `Representation.Category.FiniteIndexSemisimplicity` |
| `Representation.Character.SeparationProof` |
| `Representation.Character.TransportProof` |
| `Representation.Classification.CommonImageMultiplicityOneProof` |
| `Representation.Classification.ConstituentCompatibilityAlgebraicProof` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` |
| `Representation.Classification.CuspidalJacquetFunctorExactnessProof` |
| `Representation.Classification.CuspidalJacquetMultiplicityProof` |
| `Representation.Classification.HeadQuotientCriterionProof` |
| `Representation.Classification.IrreducibleProductEmbedding` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapProof` |
| `Representation.Classification.MultiplicityOneConstituentProof` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationProof` |
| `Representation.Classification.OppositeJacquetQuotientDetectionProof` |
| `Representation.Classification.SegmentConstituentCentralCharacterProof` |
| `Representation.Classification.SegmentFullJacquetProof` |
| `Representation.Classification.SegmentInductionAdmissibilityProof` |
| `Representation.Classification.SegmentJacquetMultiplicityProof` |
| `Representation.Classification.SegmentTensorReversalProof` |
| `Representation.Classification.SegmentTensorStabilizerProof` |
| `Representation.Classification.SegmentZelevinskyConstituentExistenceProof` |
| `Representation.Classification.SupercuspidalContragredientProof` |
| `Representation.Classification.SupercuspidalDerivativesProof` |
| `Representation.Classification.TwistedProductCharacterTwistProof` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` |
| `Representation.Classification.TwoSegmentSocleShuffleJacquetProof` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` |
| `Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` |
| `Representation.Classification.TwoSupercuspidalProductStructureProof` |
| `Representation.Classification.UpperCuspidalJacquetMultiplicityProof` |
| `Representation.Classification.UpperJacquetSubrepresentationDetectionProof` |
| `Representation.CompactCoefficient.SemisimplicityProof` |
| `Representation.Conductor.PrincipalCongruenceBasisProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesProof` |
| `Representation.CuspidalSupport.AssociatedProof` |
| `Representation.CuspidalSupport.AssociationForwardHomProof` |
| `Representation.CuspidalSupport.AssociationLawsProof` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessProof` |
| `Representation.CuspidalSupport.ConstituentComplement` |
| `Representation.CuspidalSupport.ConstituentInduction` |
| `Representation.CuspidalSupport.ConstituentProof` |
| `Representation.CuspidalSupport.ConstituentSemisimple` |
| `Representation.CuspidalSupport.CuspidalBlockIsolationProof` |
| `Representation.CuspidalSupport.CuspidalEmbeddingProof` |
| `Representation.CuspidalSupport.CuspidalTensorAssociationProof` |
| `Representation.CuspidalSupport.CuspidalTensorProof` |
| `Representation.CuspidalSupport.CuspidalityComparisonProof` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof` |
| `Representation.CuspidalSupport.DeterminantUnitStructureProof` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerProof` |
| `Representation.CuspidalSupport.FiltrationQuasicuspidality` |
| `Representation.CuspidalSupport.HarishChandraAssembly` |
| `Representation.CuspidalSupport.HarishChandraBoundaryProof` |
| `Representation.CuspidalSupport.HarishChandraConverseProof` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` |
| `Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` |
| `Representation.CuspidalSupport.LeviTensorFactorizationProof` |
| `Representation.CuspidalSupport.LeviTensorReflectionProof` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` |
| `Representation.CuspidalSupport.MinimalJacquetProof` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` |
| `Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` |
| `Representation.CuspidalSupport.ProperInductionProof` |
| `Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` |
| `Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` |
| `Representation.CuspidalSupport.StandardJacquetComparisonProof` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` |
| `Representation.CuspidalSupport.ZeroRankEmbeddingProof` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` |
| `Representation.Derivative.LeftMixedProductDerivativeProof` |
| `Representation.Derivative.MirabolicDerivativeDetectionProof` |
| `Representation.Derivative.MirabolicHighestDerivativePairingProof` |
| `Representation.Derivative.MirabolicMinusExactnessProof` |
| `Representation.Derivative.MirabolicMinusPairingTransferProof` |
| `Representation.Derivative.MirabolicProductMinusBoundary` |
| `Representation.Derivative.MirabolicProductMinusLeftPhi` |
| `Representation.Derivative.MirabolicProductMinusLeftPsi` |
| `Representation.Derivative.MirabolicProductMinusRightBoundary` |
| `Representation.Derivative.MirabolicProductMinusRightPhi` |
| `Representation.Derivative.MirabolicProductMinusRightPsi` |
| `Representation.Derivative.MirabolicProductRestriction` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationProof` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` |
| `Representation.Filtration.GradedRefinementProof` |
| `Representation.Filtration.IntervalLiftProof` |
| `Representation.Filtration.IrreducibleMultiplicityProof` |
| `Representation.Filtration.JordanHolderComparisonProof` |
| `Representation.Filtration.JordanHolderProof` |
| `Representation.Filtration.JordanHolderTransportProof` |
| `Representation.Filtration.LengthCriterionProof` |
| `Representation.Filtration.LengthTwoMatching` |
| `Representation.Filtration.MultiplicityAdditivityProof` |
| `Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof` |
| `Representation.Filtration.MultiplicityIndependenceProof` |
| `Representation.Filtration.MultiplicityTransportProof` |
| `Representation.Filtration.QuasicuspidalVanishingProof` |
| `Representation.Filtration.SimpleMapMultiplicityDetectionProof` |
| `Representation.Filtration.SubquotientAlgebraProof` |
| `Representation.Filtration.SubsingletonProof` |
| `Representation.Filtration.ZeroFactorDeletionProof` |
| `Representation.Geometric.BlockSixDecomposableProof` |
| `Representation.Geometric.BruhatMatrixExistenceProof` |
| `Representation.Geometric.BruhatWeylReflectionProof` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` |
| `Representation.Geometric.GeometricLemmaProof` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` |
| `Representation.Geometric.MonotoneBlocksProof` |
| `Representation.Geometric.OrbitSectionExtensionProof` |
| `Representation.Geometric.PadicCorrectionCancellationProof` |
| `Representation.Geometric.PadicParabolicBruhatProof` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` |
| `Representation.Geometric.ParabolicSupportGradedProof` |
| `Representation.Geometric.ParabolicSupportJacquetProof` |
| `Representation.Geometric.StandardIntersectionsProof` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` |
| `Representation.Geometric.WeylUniquenessProof` |
| `Representation.Hecke.CommonInvarianceProof` |
| `Representation.Induction.CharacterTwistProof` |
| `Representation.Induction.CompactAutomorphismIntegralProof` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` |
| `Representation.Induction.CompactLocalSectionSpanningProof` |
| `Representation.Induction.CompactQuotientProof` |
| `Representation.Induction.CompactScalarProof` |
| `Representation.Induction.CompactSurjectivityProof` |
| `Representation.Induction.CompactTransitivityProof` |
| `Representation.Induction.FiniteProductTensorBijectiveProof` |
| `Representation.Induction.NormalCoinvariantKernelProof` |
| `Representation.Induction.NormalCoinvariantProof` |
| `Representation.Induction.OppositeProductReversalProof` |
| `Representation.Induction.SplitQuotientProof` |
| `Representation.Induction.SplitStagesCharacterComparison` |
| `Representation.Induction.SurjectivityProof` |
| `Representation.Jacquet.BlockCompressionProof` |
| `Representation.Jacquet.BlockPowerKernelProof` |
| `Representation.Jacquet.CanonicalLiftBijectivityProof` |
| `Representation.Jacquet.CanonicalLiftGroupTransportProof` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof` |
| `Representation.Jacquet.CompactCompressionStableDualityProof` |
| `Representation.Jacquet.CompressionStabilizationProof` |
| `Representation.Jacquet.ExactProof` |
| `Representation.Jacquet.LocalizationExactnessProof` |
| `Representation.Jacquet.OppositeCanonicalLiftProof` |
| `Representation.Jacquet.ReciprocityProof` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftProof` |
| `Representation.Jacquet.RefinedOppositeCompressionProof` |
| `Representation.Jacquet.RefinedOppositePowerKernelProof` |
| `Representation.Jacquet.RefinedOppositeStableImageProof` |
| `Representation.MatrixCoefficient.NormRegularityProof` |
| `Representation.Parabolic.InverseTransposeProductProof` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` |
| `Representation.Parabolic.NaturalInductionDualityProof` |
| `Representation.Parabolic.NaturalJacquetDualityProof` |
| `Representation.Parabolic.NormalizedAdmissibilityProof` |
| `Representation.Parabolic.NormalizedJacquetAdmissibilityProof` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityProof` |
| `Representation.Parabolic.OppositeRefinementTransitivityProof` |
| `Representation.Parabolic.OrderedProductRegroupingProof` |
| `Representation.Parabolic.QuotientCompactProof` |
| `Representation.Parabolic.RefinedInductionTensorProof` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationProof` |
| `Representation.Parabolic.RefinementInductionTransitivityProof` |
| `Representation.Parabolic.SecondAdjointnessProof` |
| `Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof` |
| `Representation.Parabolic.UnipotentFiniteContainment` |
| `Representation.RankinSelberg.EqualRankFrobeniusProof` |
| `Representation.RankinSelberg.GeneralLinearUnimodularity` |
| `Representation.RankinSelberg.HaarSymmetriesProof` |
| `Representation.RankinSelberg.LastRowCompactOrbitProof` |
| `Representation.RankinSelberg.UnipotentUnimodularity` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffProof` |
| `Representation.Schur.CountableDimensionProof` |
| `Representation.Smooth.Contragredient.AdmissibleDualityProof` |
| `Representation.Smooth.Contragredient.ExactProof` |
| `Representation.Smooth.Contragredient.GelfandKazhdanProof` |
| `Representation.Smooth.Contragredient.HomDualityProof` |
| `Representation.Smooth.Contragredient.InvariantPairingProof` |
| `Representation.Smooth.Factorization.TwoFactorExistenceProof` |
| `Representation.Smooth.FixedVectors.FiniteTypes` |
| `Representation.Smooth.FixedVectors.GenerationInheritance` |
| `Representation.Smooth.Schur.Proof` |
| `Representation.Smooth.SmallRealizationProof` |
| `Representation.Tensor.ExternalMapSurjectivityProof` |
| `Representation.Tensor.SmoothDualInjectivityProof` |
| `Representation.Tensor.SmoothDualSurjectivityProof` |
| `Representation.Tensor.UnitaryProof` |
| `Representation.Twist.AdmissibilityProof` |
| `Representation.Twist.SubquotientProof` |
| `Representation.Unitary.CentralCharacterProof` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationProof` |
| `Representation.Unitary.SquareIntegrableProof` |
| `Representation.Unitary.SupercuspidalRealUnitarizationProof` |
| `Representation.Unitary.UnitarizabilityContinuationProof` |
| `Representation.Unramified.SphericalConstituentExistenceProof` |
| `Representation.Whittaker.BruhatCellFactorizationProof` |
| `Representation.Whittaker.BruhatCellInvarianceProof` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingProof` |
| `Representation.Whittaker.BruhatCellVanishingProof` |
| `Representation.Whittaker.BruhatCompatibleSupportProof` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceProof` |
| `Representation.Whittaker.BruhatHaarMeasureProof` |
| `Representation.Whittaker.BruhatOrbitalIntegrationProof` |
| `Representation.Whittaker.CompatibleMonomialFixedProof` |
| `Representation.Whittaker.DistributionInvarianceProof` |
| `Representation.Whittaker.GeneralizedCoefficientKernelProof` |
| `Representation.Whittaker.MultiplicityOneProof` |
| `Topology.GroupAction.FiniteOrbitProof` |
| `Weil.Representation.ContinuityProof` |
| `Weil.Representation.IsomorphismInvarianceProof` |
| `Weil.Representation.OperationClosureProof` |

The second table lists the 30 further closure modules that prove a named
Library proposition but are not the entry module of a proof. It includes every
remaining closure module whose name ends in `Proof`. They are early modules of
the Library, or helper modules of a later proof. For each, the table gives the
proposition it proves or the proof it serves. Twenty-nine of these rows lie
in the closure of the S1 proof and repeat the S1 proof's audit. The row
`ConstituentRankZero` was added for the modules outside that closure.

| Proved module | Provenance |
| --- | --- |
| `Galois.FiniteField.ComparisonProof` | proves `FrobeniusComparison` (module `Galois.FiniteField.Comparison`); imported by `Weil.Local.Assembly` |
| `Galois.Local.SpectralProof` | proves `SpectralResidueExactness` |
| `Group.GL.Nonarchimedean` | statement module `Group.GL.NonarchimedeanStatement` (`ValuativeGeneralLinearNonarchimedean`) |
| `LocalField.Normalization.Proof` | proves `PadicNormalizationStatement` |
| `Representation.Compact.ProjectionProof` | proves the proposition of `Representation.Compact.ProjectionStatement` |
| `Representation.Compact.SurjectivityProof` | proves the proposition of `Representation.Compact.SurjectivityStatement` |
| `Representation.CuspidalSupport.ConstituentRankZero` | proves the rank-zero case `leviCuspidalConstituent_rankZero` of `LeviCuspidalConstituentTheorem`; helper of `CuspidalSupport.ConstituentProof`, which uses it for rank zero |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` | proves `DeterminantUnitCornerStructureStatement` (BZ76 Lemma 4.9); helper of `CuspidalSupport.CompactCoefficientFinitenessProof` |
| `Representation.CuspidalSupport.HarishChandraForwardProof` | helper of `CuspidalSupport.HarishChandraAssembly`; its theorems take the Cartan decomposition as a hypothesis, which the assembly discharges |
| `Representation.Jacquet.RefinedUpperCanonicalLiftProof` | helper of `Parabolic.NaturalJacquetDualityProof`; adds no statement |
| `Representation.Jacquet.StablePairingProof` | helper of `Parabolic.NaturalJacquetDualityProof`; adds no statement |
| `Representation.MatrixCoefficient.LawsProof` | proves the proposition of `Representation.MatrixCoefficient.LawsStatement` |
| `Representation.Smooth.Admissibility.CofinalProof` | proves the proposition of `Representation.Smooth.Admissibility.CofinalStatement` |
| `Representation.Smooth.Admissibility.EmbeddingProof` | proves `AdmissibleSubrepresentationStatement` |
| `Representation.Smooth.Admissibility.EquivalenceProof` | proves the proposition of `Representation.Smooth.Admissibility.EquivalenceStatement` |
| `Representation.Smooth.Contragredient.CompactDualityProof` | statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | proves the proposition of `Representation.Smooth.Contragredient.LawsStatement` |
| `Representation.Smooth.FixedVectors.LawsProof` | proves the proposition of `Representation.Smooth.FixedVectors.LawsStatement` |
| `Representation.Smooth.FixedVectors.OrderProof` | proves the proposition of `Representation.Smooth.FixedVectors.OrderStatement` |
| `Representation.Smooth.SmoothPart.BasicProof` | proves the proposition of `Representation.Smooth.SmoothPart.BasicStatement` |
| `Representation.Smooth.Transfer.PullbackProof` | proves the proposition of `Representation.Smooth.Transfer.PullbackStatement` |
| `Representation.Smooth.Transfer.SubquotientProof` | proves the proposition of `Representation.Smooth.Transfer.SubquotientStatement` |
| `Representation.Twist.AlgebraProof` | proves the proposition of `Representation.Twist.AlgebraStatement` |
| `Representation.Twist.ContinuousCharacterProof` | proves `ContinuousComplexCharacterOpenKernel` |
| `Representation.Twist.DualProof` | proves the proposition of `Representation.Twist.DualStatement` |
| `Representation.Twist.PullbackProof` | proves the proposition of `Representation.Twist.PullbackStatement` |
| `Representation.Twist.SmoothProof` | proves `TwistSmoothCompatibility` |
| `Topology.CompactOpen.NeighborhoodBasis` | proves the proposition of `Topology.CompactOpen.NeighborhoodBasisStatement` |
| `Weil.AlgebraicProof` | proves `AlgebraicProperties` (module `Weil.Algebraic`) |
| `Weil.TopologyProof` | proves `TopologyProperties` (module `Weil.Topology`) |

None of the modules in the second table proves an excluded result. To find these
modules, theorem declarations were scanned for types that are proposition
definitions of a `…Statement` module. The same scan, together with a scan of
theorem hypotheses, finds only conditional reductions besides the modules of
the two tables. Each proves a named proposition or one of its consequences from
explicit theorem-valued hypotheses:

- the helper modules of this proof with hypotheses: `JuxtaposedConditionalAssembly`,
  `JuxtaposedJacquetCover`, `JuxtaposedJacquetPositivity`,
  `JuxtaposedNonadjacentPairIrreducible`, `JuxtaposedUnionSeparation` and
  `JuxtaposedUniqueProperSub` assume named Library statements, and the swap
  modules assume `hswap` or `hirr`. This module and
  `juxtaposedSegmentSocleReverseProductStructure_of_irreducible` discharge all of
  them with the published theorems of the direct-input table;
- `Classification.JuxtaposedUnionHead`, `Classification.JuxtaposedDecreasingQuotient`
  and `Classification.SegmentSocleDecreasingHead` (supporting modules of this
  proof). They
  assume `SegmentZelevinskyConstituentExistence`, which
  `JuxtaposedConditionalAssembly` supplies as the published
  `segmentZelevinskyConstituentExistence`;
- `CuspidalSupport.AssociationForwardHomSupport`. It assumes
  `LeviCuspidalConstituentTheorem`, which its user
  `CuspidalSupport.AssociationForwardHomProof` supplies as the published
  `leviCuspidalConstituentTheorem`;
- the fourteen conditional modules in the closure of the S1 proof, listed in its
  audit: `Classification.NonadjacentLeibnizPieces`,
  `Classification.NonadjacentTwoBlock`,
  `Classification.SegmentEdgeJacquetReduction`,
  `Classification.SegmentFullJacquetEdgeData`,
  `Classification.TwoSegmentShuffleAssembly`,
  `Classification.TwoSupercuspidalAdjacentStructure`,
  `CuspidalSupport.AssociatedConditional`,
  `CuspidalSupport.CompactCoefficientFinitenessReduction`,
  `Derivative.LeftMixedProductHigher`, `Derivative.LeftMixedProductVanishing`,
  `Geometric.CosetOrbitOrdering`, `Parabolic.NaturalInductionDualityFromScalar`,
  `Parabolic.SecondAdjointnessAssembly` and
  `Smooth.Contragredient.GelfandKazhdanAssembly` (all under `Representation.`).
  Wherever the closure uses one of them, a proof module of the first table or
  the S1 proof discharges its hypotheses with published theorems.

## Development check

A build over Library commit `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` built
this module and its
fourteen helper modules with no errors or warnings. Inspection of
`Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure`
reports a theorem with level parameters `uF, uV` and the axioms `propext`,
`Classical.choice` and `Quot.sound` only.
