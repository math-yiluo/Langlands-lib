# Zelevinsky 1980, Proposition 4.6, step (1): the juxtaposed case, proof

Author: Worker 1032, first executor of task
`0c90f7e4-78fa-43fd-8736-238bb3e8617d`. This module and the fourteen helper
modules `Juxtaposed*` submitted with it are Worker 1032's own work. Worker 167,
the task's second executor, wrote the supporting units that were published
under this task and that the proof imports. They are listed in the dependency
audit below. Some of them adapt drafts of Worker 1032. Every other input is a
published declaration imported by its Lean name, and no code of another author
is copied.

## Statement proved

```lean
theorem Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure.{uF,uV} F T`
of `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement`
(statement artifact `fa568a15-0e47-4b43-9094-80e38892004e`, arrangement task
`7ff2a1e9-89dc-439e-a861-a567b3db92bf`). The statement pair and every pair it
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
  `twoSegmentSocleShuffleJacquet F T` of task
  `343ddfde-e74c-46b8-a559-0c8f3a3145a6`. Lean fixes its third universe to
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
`segmentFullJacquetFormula` (Zelevinsky 3.1) and Worker 167's
`exists_juxtaposedUnionHead`. The last one is applied to
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
9. *Union datum and head* (`exists_juxtaposedUnionHead`, Worker 167). For
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
(module `Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`, proof
artifact `98cc1114-db18-414e-8ad5-ddb3f559e47d`, task
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`). Its proof uses the Bernstein–Zelevinsky
derivative theory. This proof imports the theorem by name. Neither this module
nor its helper modules state, construct or prove anything about derivatives.

It is admissible here for the following reasons, recorded by the trusted
operator in response `35fea30f10ab5d0bad9243914018480c` to request
`e700b5a575f15ab18c2545dba6db60c8`. The task's "do not use or duplicate
derivative work" governs this proof's own argument and the derivative
constructions owned by Workers 357 and 758. It does not exclude published,
independently accepted results that were proved through derivatives. The task
itself requires reusing the published proof of Zelevinsky 3.1, and its module
`SegmentFullJacquetProof` already imports `TwoSupercuspidalProductStructureProof`
and through it `TwoSupercuspidalNonadjacentIrreducibilityProof`. So 1.11(a) adds
no module to the closure of this proof (verified below). Task `3c9849a4` is not
among the exclusions. The operator's conditions are met. The theorem is
imported by name, this proof adds no derivative construction or argument of its
own, and the closure of 1.11(a) is part of the audit below.

## Dependency audit

All counts and checks below refer to Library commit
`47b67c4eb87954cf163f3a88bb94b9cbae2edbf0`, which contains the published S1
proof `Classification.TwoSegmentSocleShuffleJacquetProof`, together with this
candidate's fifteen modules. Module names omit the prefix `Langlands.`.

### Direct inputs

The proof modules imported by this module or its fourteen helper modules, and
what the proof takes from each:

| Input (module) | Artifact, task | Use |
| --- | --- | --- |
| `twoSegmentSocleShuffleJacquet` (`Representation.Classification.TwoSegmentSocleShuffleJacquetProof`) | proof `7bd68d8d`, task `343ddfde-e74c-46b8-a559-0c8f3a3145a6` (Workers 1142 and 1145) | `hS1`, Zelevinsky 1.6 and 3.1 for two segment socles |
| `twoSupercuspidalNonadjacentProductIrreducible` (`Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`) | proof `98cc1114`, task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` | `hirr`, Zelevinsky 1.11(a) |
| `segmentFullJacquetFormula` (`Representation.Classification.SegmentFullJacquetProof`) | proof `f2c2886a`, task `b331611c-526d-4925-87fe-ea67ed6e6fed` (Workers 890 and 964) | clause 1, Zelevinsky 3.1, for `J(e.induced)` |
| `segmentZelevinskyConstituentExistence` (`Representation.Classification.SegmentZelevinskyConstituentExistenceProof`) | proof `7172c4a6`, task `4ca79bbd-589e-476b-9f65-661e799984b5` | existence of `⟨U⟩` with its socle and head, input of `exists_juxtaposedUnionHead` |
| `CuspidalSupport.nonassociatedJacquetSubquotients` (`Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof`) | proof `8c6610e7`, task `b17b8c8c-858b-4b48-994b-e3641cb05f02` | BZ77 2.13(b), positivity (step 6) |
| `CuspidalSupport.minimalNonzeroJacquet` (`Representation.CuspidalSupport.MinimalJacquetProof`) | proof `dd0f42fe`, task `f28607f5-1eef-4329-ae18-2576ef25ab6a` | BZ77 2.14, positivity (step 6) |
| `CuspidalSupport.glCuspidalTensor` (`Representation.CuspidalSupport.CuspidalTensorProof`) | proof `8513f998`, task `cece816e-aee9-40ca-9139-d770491b6178` | shuffle tensors are irreducible and quasicuspidal |
| `CuspidalSupport.glCuspidalTensorAssociation` (`Representation.CuspidalSupport.CuspidalTensorAssociationProof`) | proof `e209fa9f`, task `ee36e054-716f-492a-a0e3-e83b614d9431` | factorwise comparison of cuspidal tensors (step 2) |
| `segmentTensorStabilizerAndCuspidality` (`Representation.Classification.SegmentTensorStabilizerProof`) | proof `1e385864`, task `67279e36-f3c2-42e3-9302-11729784042e` | `segmentSupercuspidalFactor`, injectivity of integral twists |
| `irreducibleTwoFactorProductSwap` (`Representation.Classification.IrreducibleTwoFactorProductSwapProof`) | proof `be6157e1`, task `0988a3e0-a086-474d-b2d2-7e53902b43cb` | two-block swap (step 4) |
| `Parabolic.orderedProductRegrouping` (`Representation.Parabolic.OrderedProductRegroupingProof`) | proof `3c33bc41`, task `2ef80e63-ce40-401c-8203-4cac37fb0307` | regrouping of products (steps 3 and 4) |
| `irreducibleProductEmbedding` (`Representation.Classification.IrreducibleProductEmbedding`) | proof `18400cbf`, task `974d403b-305c-4c06-8dff-d4efb438993f` | its lemma `normalizedProduct_embedding_of_factor_embeddings` (step 3) |
| `jordanHolderSimpleMapDetection` (`Representation.Filtration.SimpleMapMultiplicityDetectionProof`) | proof `f1afeb6f`, task `67279e36-f3c2-42e3-9302-11729784042e` | its lemma `jordanHolderSubobjectSimpleMapDetection` (step 5) |
| `multiplicityFreeSubmoduleLattice` (`Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof`) | proof `ccd92a0c`, task `0d7093cf-8a18-4d0f-ba5b-20b24b49f969` | lattice of a multiplicity free module (step 7) |
| `multiplicityTransport` (`Representation.Filtration.MultiplicityTransportProof`) | proof `1905b374`, task `b8ecf398-d8ff-48bd-a6b3-5da6557b7655` | its lemma `equivJordanHolderMultiplicityTransport` (step 7) |
| `LengthTwo.lengthTwoFactorMatchingCriterion` (`Representation.Filtration.LengthTwoMatching`) | proof `701ca674`, task `53969569-6b54-45b3-a1f8-89f1fe96a1f8` | its two-step filtration `LengthTwo.twoStep` with `twoStep_hasSimpleFactors`, and lattice lemmas (step 10) |

The helper modules also import the following Library modules, which carry no
proof record of their own. `CuspidalSupport.InducedJacquetEvaluation` (Worker
241) contributes `exists_ne_zero_normalizedJacquet_hom` (step 5), and
`CuspidalSupport.InducedJacquetCount` contributes
`one_le_jacquetLength_of_isSubquotient` (step 6). Both are lemma modules of the
cuspidal-support development. The rest are definition modules:
`CuspidalSupport.JacquetLengthDetector` (`23b07dbb`),
`CuspidalSupport.LeviAssociation` (`cbbf9618`), `Induction.SingleBlock`
(`fcc278b3`), `Filtration.ConstituentSupportDefinitions` (`382e9baf`),
`Classification.Segments` (`556c1561`) and
`Group.GL.AdjacentMergeShape` (`be467b6b`). The statement modules imported are
the target's, `TwoSegmentSocleShuffleJacquetStatement` (`2081c976`),
`SegmentFullJacquetStatement` (`b4d59526`) and
`TwoSupercuspidalProductStructureStatement` (`7ec90a07`).

Supporting units published under this task `0c90f7e4` and imported by the proof:

| Module | Supporting unit | Author |
| --- | --- | --- |
| `Representation.Classification.JuxtaposedUnionDatum` | `2da8d833` | Workers 167 and 1032 |
| `Representation.Classification.JuxtaposedUnionHead` | `83f94e0a` | Workers 167 and 1032 |
| `Representation.Classification.SegmentSocleDecreasingHead` | `33cb04d0` | Worker 167 |
| `Representation.Classification.JuxtaposedDecreasingQuotient` | `3a5d5326` | Worker 167, adapting a draft of Worker 1032 |
| `Representation.Classification.JuxtaposedRefinementTools` | `49643601` | Worker 167, extracted from Worker 1032's drafts |

The closure of the S1 proof contains eight further units of Worker 167 filed
under this task: `TwoSourceShuffleLabels` (`6324c466`), `UniformJacquetVanishing`
(`7474c907`), `UniformRefinementCombinatorics` (`18231764`),
`UniformRefinementCoordinates` (`a5dd707e`), `UniformRefinementLeviTransport`
(`de9b4338`), `UniformRefinementShuffleRealization` (`ceacade2`),
`UniformRefinementSurvivors` (`e4622c15`) and `UniformTargetBlockLabels`
(`c4f50f7f`). All thirteen units of this task in the closure are
definition-kind units with finite coordinates, segment data, transport, head and
vanishing lemmas. None of them states or assumes the target of this task.

### Import closure

A recursive scan of the `import` lines gives 1145 project modules in the
transitive closure, this module included. The closures of its four direct
imports have these sizes:

- `JuxtaposedConditionalAssembly`: 1130 modules. It contains the closure of
  `SegmentFullJacquetProof` (1038 modules), which contains the closure of
  Zelevinsky 1.11, `TwoSupercuspidalProductStructureProof` (879 modules).
- `TwoSegmentSocleShuffleJacquetProof`: 1055 modules. Thirteen of them lie
  outside the closure of `JuxtaposedConditionalAssembly`: the S1 proof module,
  its two supporting units `TwoSegmentShuffleAssembly` and
  `TwoSegmentShufflePieces`, the eight units of Worker 167 listed above other
  than `JuxtaposedRefinementTools`, `Geometric.WholeLeviPieceTransport` and
  `CuspidalSupport.QuasicuspidalJacquetVanishingProof`.
- `JuxtaposedNonadjacentPairIrreducible`: 297 modules.
- `TwoSupercuspidalNonadjacentIrreducibilityProof` (1.11(a)): 656 modules, all
  inside the closure of `SegmentFullJacquetProof`. So 1.11(a) adds no module.

Of the 1130 published modules in the closure, the Library registry records 273
as the entry module of a published proof, 355 as that of a published
definition or supporting unit and 241 as that of a published statement. The
remaining 261 are helper modules shipped with these artifacts, or modules from
the project's first proof rounds, which have no current registry record.

### Exclusions

The checks below cover all the exclusions of this task: the tasks `a55c4267`,
`8fa9f68b`, `2ae5cbe5`, `e3634665`, `cded83f3`, `426911b4`, `66e3b87c`,
`c84cd52c`, `6780b79c`, `23189526`, `f3a69bc8`, `aca8805b`, `3bfb61fa`,
`ebea9a8a`, `20e4e1c6`, `52e97845`, `1cb45da2`, `cd8ab97c`, `bf433f0a` and
`8364e73f`, and `LinkedSegmentSocleReverseProductQuotientHom` with its proof
successor.

- *Artifacts of the excluded tasks.* Every excluded task was inspected, and the
  modules of each of its artifacts were compared with the closure. No statement
  or proof artifact of an excluded task has a module in the closure. In
  particular, the accepted proof `58f5a9ff` of task `23189526` and the eight
  accepted proofs of task `aca8805b` are outside it. The only matches are seven
  definition-kind modules filed under the socle-exhaustion task `f3a69bc8`,
  explained below. Tasks `8fa9f68b`, `6780b79c`, `66e3b87c`, `cd8ab97c` and
  `bf433f0a` have no artifacts.
- *Proof owners.* All 273 proof records of the closure (first inventory table
  below) belong to tasks that are not excluded.
- *Declaration names.* The Lean files of the closure were searched for the
  targets of the excluded tasks: `LinkedSegmentSocleReverseProductStructure`,
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
- *Task identifiers in Lean files.* No Lean file of the closure contains any
  excluded task-ID prefix.

Definition-kind modules filed under the socle-exhaustion task
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`:

- `Combinatorics.RelationInversions` (`9e971abc`, Worker 494),
  `Representation.Classification.SegmentIntegralCoordinates` (`3fbc6255`),
  `Representation.Classification.SegmentIntervalLinkage` (`ae9bf46e`) and
  `Representation.Classification.SegmentReplacementInversions` (`8bbacdd5`).
  The target statement module imports `SegmentReplacementInversions`, which
  defines `IsUnionIntersectionReplacement` and imports the other three directly
  or transitively. They are in the closure of the target statement itself, so no
  proof of it can avoid them.
- `Representation.Classification.SegmentUnionIntersection` (`11e64379`) and
  `Representation.Classification.SegmentProductReplacement` (`bc3563a2`), both
  by Worker 494. They are the actual union/intersection segments and the
  segment-product replacement data. `JuxtaposedUnionDatum` uses them to build `U`
  and `e`.
- `Representation.Filtration.ObjectTransport` (`68054cb0`). It pulls an object
  filtration back along a monoid homomorphism and transports it along an
  equivalence. The closures of Zelevinsky 1.11 and 3.1 reach it through
  `NonadjacentSpecialization` and `OppositeCuspidalJacquetFiltrationProof`, and
  the S1 closure through `Tensor.ProductFiltration`.

These modules contain segment coordinates, interval combinatorics, inversion
counts, replacement data and filtration transport. None states, proves or
assumes `MultisegmentSocleExhaustion` or any other excluded result, and their
imports contain nothing from an excluded task. They are generic lower
infrastructure, not conclusions or proofs of an excluded task.

An earlier draft imported Worker 167's `Filtration.ObjectRepFiltrationTwoStep`,
which imports `Filtration.FunctorLengthTwoDetection`. That abstract lattice
module was published inside definition `d910a6a8` of the excluded task
`a55c4267`. This proof does not import either module. The four facts it
needed (`quotientRepBotEquiv`, `topSubrepresentationEquiv`,
`subrepresentation_ne_bot_of_isIrreducible`, `eq_bot_or_eq_of_le_isIrreducible`)
are proved directly in `JuxtaposedConditionalAssembly`. So no artifact of task
`a55c4267` is in the closure.

There is no circularity. None of the closure modules imports this module, and
none assumes the target proposition.

### Derivative results

This module and its fourteen helper modules state, construct and prove nothing
about derivatives, and they use no derivative result directly. The closure
contains 158 modules whose names contain `Derivative`, `Mirabolic`,
`Whittaker` or `GelfandKazhdan`. All of them lie inside the closure (879
modules) of Zelevinsky 1.11, `twoSupercuspidalProductStructure` (module
`TwoSupercuspidalProductStructureProof`, proof `f10f67f3`, task
`ab61f565-1427-4746-ba77-46097563e962`). It proves BZ77 Theorem 4.2 with the
published Bernstein–Zelevinsky derivative theory. The task-mandated input
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
no registry record of the closure belongs to tasks `209027ca` (Zelevinsky 3.5),
`60b25b28` (Zelevinsky 4.3), `f81d9b36` (BZ77 4.7(b)), `4e152d19` or
`8e5b4563`. The derivative modules inside the 1.11 closure are published and
independently accepted, and none of them is a hypothesis of any step of this
proof.

### Proved-module inventory

The first table lists every closure module that the Library registry records
as the entry module of a published proof (273 modules), with its proof artifact
and the task it was proved under. None of these tasks is excluded.

| Proved module | Proof artifact | Task |
| --- | --- | --- |
| `Algebra.SandwichDimensionBoundProof` | `a4c517c5` | `21b68369-cc3e-42af-8d47-03a5bb4d8d34` |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | `a9cc9564` | `071e4d23-2827-49e3-953a-b755c243d302` |
| `Analysis.Local.QuotientAutomorphismProof` | `9eef24ba` | `88e8f6c0-c9cf-40fb-90e5-2ddbb72cc479` |
| `Analysis.Local.QuotientAveragingKernel` | `e260634d` | `4ecaafca-57e4-472e-9501-7cf362d21007` |
| `Analysis.Local.QuotientMeasureExistence` | `675cd3b8` | `7d14a606-bb49-4cf0-9f89-8034e21e9f15` |
| `Analysis.Local.QuotientPositiveLifting` | `e8eb5c9d` | `40466063-2de2-456b-ae79-93c782b76e0b` |
| `Galois.Local.AbsoluteProof` | `f92d202b` | `784bfe1b-4a1c-4925-8b83-5e2fbbb2de91` |
| `Group.GL.BlockContractionProof` | `92813962` | `7cb3dbc0-fae7-4e88-a79f-d0dcc19aaee5` |
| `Group.GL.BlockIwahoriBasis` | `c110ea11` | `9c364114-a50b-4402-ac9b-63b12dfb9484` |
| `Group.GL.BlockModulusHaarProof` | `3008bd3f` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.BlockUnipotentHaarProof` | `69cecf67` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.CartanProof` | `fd42961a` | `506fa0e8-79ea-41fb-85da-18cc6dadceab` |
| `Group.GL.CentralQuotientTopologyProof` | `7fe122eb` | `6ee0f696-9c8a-40ab-b8d0-210ae1ecd734` |
| `Group.GL.CountabilityProof` | `dd877404` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Group.GL.InverseTransposeIwahoriProof` | `ee599ebf` | `05abc80d-aec1-4f31-92fc-846b13a15ec2` |
| `Group.GL.MirabolicMixedOrbitCoverageProof` | `2178f392` | `b7304e81-6082-4291-834f-fff6f448590b` |
| `Group.GL.MirabolicModularCharacterProof` | `bfba0d9f` | `518f986d-21ce-44ac-bd2e-80e6b1e15561` |
| `Group.GL.MirabolicModulusProof` | `f25fdd6c` | `f947a735-872d-44db-a9ea-954d17dec4bd` |
| `Group.GL.PrincipalBlockFactorizationProof` | `c4f3e890` | `069d1e18-b908-42cb-b064-af1237ba4e7c` |
| `Group.GL.UpperBruhatBoundaryProof` | `1200687b` | `2fe252f9-125b-47cf-9277-20271ef24b1b` |
| `Group.GL.UpperBruhatCoordinatesProof` | `3dbfe83b` | `fd59b42f-6374-40fa-91ea-0dd9de25ea17` |
| `Group.GL.UpperBruhatFiltrationGeometryProof` | `0bfabde5` | `804989b0-fc9d-4e19-b339-ddddb5f0e143` |
| `Group.GL.UpperBruhatLocalClosednessProof` | `c95cbd74` | `080c7802-956c-4b53-8077-3535aebc8f2b` |
| `Group.GL.UpperBruhatPivotProof` | `3cb9fdc0` | `cb1e92a3-bf5e-4765-a993-c41522dd0022` |
| `Group.GL.UpperBruhatProof` | `870ed2b8` | `8c2f6593-d22c-44b1-be0b-4ad6cb08445f` |
| `Group.GL.UpperBruhatRankProof` | `bf240f56` | `5ded0ee0-107f-4026-8f4d-2914271951e0` |
| `Group.GL.UpperBruhatTransposeProof` | `fb12f422` | `a0748df8-d292-4712-b136-5d497f20c6e7` |
| `Group.GL.UpperUnipotentCompactContainmentProof` | `5245f863` | `4d4af694-8d02-4337-86cb-260fe32fdbea` |
| `Group.GL.UpperUnipotentFactorizationProof` | `bca2c4cb` | `a8e4c0ca-ae06-4409-a11f-83ea76aefd10` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof` | `f19bf4cc` | `bfcbbf63-ceae-4164-a704-2df59ca54f67` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof` | `c6cadd36` | `71db8a18-f07f-4ab5-903a-dad529415e84` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof` | `a8683405` | `0b4011fc-a687-4bd8-b8b3-d1516f7cc6cd` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` | `f5ed0e18` | `7ce05a8f-e5f8-4e6b-a8d4-d09cba4a5b8e` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionProof` | `9f1d0056` | `e30739f3-023e-4ab9-8420-03f4b6371108` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentProof` | `9f406413` | `3c0bd25b-3ebd-49a0-800a-966e900dbb39` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof` | `2cc18a52` | `51a122ec-9363-4c38-9df9-593ffdb99219` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityProof` | `ec24ad2f` | `af88fd57-87dd-4c4a-8a43-76f66553d80f` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingProof` | `0dcd54e0` | `4135f71e-a810-48af-8bd6-a199c17327da` |
| `HarmonicAnalysis.Distribution.LocalizationProof` | `8f3e3767` | `0c56480a-d0f8-4156-be1b-c331baa7dadd` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof` | `46428fca` | `b559bab6-0abe-483a-b982-d9b9c83187f0` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof` | `a18c6361` | `63fd1dbc-b930-474b-bfb0-6728e917a2e2` |
| `HarmonicAnalysis.Distribution.TransposeInvariantProof` | `a273f153` | `f9ba6d55-99f2-4ae7-93ad-0878f9bc7eb9` |
| `HarmonicAnalysis.PadicAdditiveConductorProof` | `8f35e474` | `e74b11cc-3905-4817-b499-dd50ea4f55f0` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | `4d3a028e` | `0e28951e-9779-4567-b8b0-c95334854fac` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | `391187ae` | `574c1368-49a7-48eb-a084-18006b0f2871` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` | `72e1678f` | `2dbce78d-1f86-48f6-94e1-f32abb3be555` |
| `HarmonicAnalysis.RowTensorDecompositionProof` | `5d850fc9` | `3d0044b1-369c-4dc6-9f09-db47aec3ad6d` |
| `HarmonicAnalysis.RowTestSmoothProof` | `903c63ec` | `5998b0b2-e367-4e85-8d4d-47e3b9b4a222` |
| `HarmonicAnalysis.TriangularTranslationProof` | `59aa9379` | `7f443547-d49c-4edd-ba7e-9f0fb9d6ad67` |
| `LinearAlgebra.CyclicQuotientPairingProof` | `b1614c57` | `04ac0d48-00f1-428b-9d7e-afdfee7e4512` |
| `LinearAlgebra.MatrixAEvalConjugacyProof` | `5177f474` | `e82ee8d6-204c-40ac-85b0-968fb0a6a298` |
| `LinearAlgebra.MatrixCharpolyConjugacyProof` | `bbdcaa84` | `e82ee8d6-204c-40ac-85b0-968fb0a6a298` |
| `LinearAlgebra.MatrixTransposeConjugateProof` | `ffe32e49` | `a6652e7a-61f5-408f-a2b2-bfe81c3a2361` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof` | `da74a1b6` | `6ec62b7e-e127-438d-9e71-f96ea2435fab` |
| `LocalField.SmoothCharacterNormProof` | `92aab2ff` | `fc38422f-e429-4f03-8033-8e5dbbb6c12c` |
| `Representation.Category.ConstituentDichotomy` | `50f28903` | `075b1ece-5f28-4417-b9ef-c56b6f683d1b` |
| `Representation.Category.FiniteIndexSemisimplicity` | `4a6cbfbb` | `f3234a03-eca9-417d-b111-c370098cb5c9` |
| `Representation.Character.SeparationProof` | `a68eef2b` | `50357f3e-0d26-4004-8ca0-562b7c8c3045` |
| `Representation.Character.TransportProof` | `83f963a8` | `25af224a-861b-48d6-9a6f-76284babdde5` |
| `Representation.Classification.CommonImageMultiplicityOneProof` | `8275fce5` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.ConstituentCompatibilityAlgebraicProof` | `c58d850a` | `bf9c99f4-41e2-41f2-a3df-970ab1e0a022` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` | `a7545313` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.CuspidalJacquetFunctorExactnessProof` | `2fda347f` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.CuspidalJacquetMultiplicityProof` | `ee0e3c5f` | `c9dbd607-82e5-4821-b367-736e876565d9` |
| `Representation.Classification.HeadQuotientCriterionProof` | `91016d01` | `751de03d-f147-4248-a488-f675241a3088` |
| `Representation.Classification.IrreducibleProductEmbedding` | `18400cbf` | `974d403b-305c-4c06-8dff-d4efb438993f` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapProof` | `be6157e1` | `0988a3e0-a086-474d-b2d2-7e53902b43cb` |
| `Representation.Classification.MultiplicityOneConstituentProof` | `01aebb89` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationProof` | `75b961f6` | `efffd9ec-2492-4b9e-9425-e52e9146406b` |
| `Representation.Classification.OppositeJacquetQuotientDetectionProof` | `bf215123` | `ea725274-e2c1-4755-bce4-b3366fc5d5c4` |
| `Representation.Classification.SegmentConstituentCentralCharacterProof` | `fb068e0c` | `5093df28-71e8-4409-8477-a2880e392688` |
| `Representation.Classification.SegmentFullJacquetProof` | `f2c2886a` | `b331611c-526d-4925-87fe-ea67ed6e6fed` |
| `Representation.Classification.SegmentInductionAdmissibilityProof` | `b44b1180` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SegmentJacquetMultiplicityProof` | `b83d6ff9` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SegmentTensorReversalProof` | `51691f48` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SegmentTensorStabilizerProof` | `1e385864` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SegmentZelevinskyConstituentExistenceProof` | `7172c4a6` | `4ca79bbd-589e-476b-9f65-661e799984b5` |
| `Representation.Classification.SupercuspidalContragredientProof` | `a090c713` | `1c921aca-ebef-4c0c-8c38-63156b8e2930` |
| `Representation.Classification.SupercuspidalDerivativesProof` | `fd42c8ef` | `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` |
| `Representation.Classification.TwistedProductCharacterTwistProof` | `ed7a2cff` | `c9fc6804-0810-4bdd-afd6-703678856df8` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` | `ee4360e4` | `a0b83fd9-00fd-4ce7-8aa6-35348b04e19f` |
| `Representation.Classification.TwoSegmentSocleShuffleJacquetProof` | `7bd68d8d` | `343ddfde-e74c-46b8-a559-0c8f3a3145a6` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` | `5d030a71` | `0988a3e0-a086-474d-b2d2-7e53902b43cb` |
| `Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` | `98cc1114` | `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` |
| `Representation.Classification.TwoSupercuspidalProductStructureProof` | `f10f67f3` | `ab61f565-1427-4746-ba77-46097563e962` |
| `Representation.Classification.UpperCuspidalJacquetMultiplicityProof` | `8445cc85` | `c9dbd607-82e5-4821-b367-736e876565d9` |
| `Representation.Classification.UpperJacquetSubrepresentationDetectionProof` | `efe3c5aa` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.CompactCoefficient.SemisimplicityProof` | `1e1f8f18` | `d5a1f78e-156e-40a1-bf22-b80779eda1ce` |
| `Representation.Conductor.PrincipalCongruenceBasisProof` | `1a11e01c` | `ec709f88-fe65-43ae-8db1-13e4baf10217` |
| `Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` | `3d3f251a` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | `d5bbef23` | `17247e03-9471-4f13-81fa-e4f7058619a0` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesProof` | `5e121583` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.AssociatedProof` | `df6d40a0` | `6fe38fdd-fc45-4d32-9221-5b7788ee51f2` |
| `Representation.CuspidalSupport.AssociationForwardHomProof` | `0b61f195` | `18476e24-f842-458b-9a71-0fb03f270b2c` |
| `Representation.CuspidalSupport.AssociationLawsProof` | `a3d0cdf6` | `944b9b06-1e87-42d1-a565-00395593eb8b` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessProof` | `a23cbcdb` | `6884361c-0ab2-41b3-8098-9c070c4a1b3e` |
| `Representation.CuspidalSupport.ConstituentComplement` | `8abcd6bd` | `bc829a98-7c9d-4968-83ad-b2fab2528fe7` |
| `Representation.CuspidalSupport.ConstituentInduction` | `7f8da371` | `db7ca8ee-7b2a-44e2-b694-e8917dbf3c26` |
| `Representation.CuspidalSupport.ConstituentProof` | `00a93329` | `fe734e49-26a6-457a-89e8-3b8e66d5cd39` |
| `Representation.CuspidalSupport.ConstituentSemisimple` | `b5db010f` | `ce991618-f970-4005-95bd-a87e2d539702` |
| `Representation.CuspidalSupport.CuspidalBlockIsolationProof` | `697877ed` | `cae15ca4-9721-444b-ab37-300b46d5a9ff` |
| `Representation.CuspidalSupport.CuspidalEmbeddingProof` | `b518020e` | `d1684637-cf80-4266-8850-2d68c922d008` |
| `Representation.CuspidalSupport.CuspidalTensorAssociationProof` | `e209fa9f` | `ee36e054-716f-492a-a0e3-e83b614d9431` |
| `Representation.CuspidalSupport.CuspidalTensorProof` | `8513f998` | `cece816e-aee9-40ca-9139-d770491b6178` |
| `Representation.CuspidalSupport.CuspidalityComparisonProof` | `b38138d8` | `e2c46108-7f86-4c0b-994d-3f34704b0261` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof` | `6a6fd8f2` | `dc05b10a-c1b1-467d-a904-a871f9d6c6e9` |
| `Representation.CuspidalSupport.DeterminantUnitStructureProof` | `cc102593` | `bb7d9bb8-8b90-41e5-8005-9d81271939af` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerProof` | `7c0d8ba0` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.CuspidalSupport.FiltrationQuasicuspidality` | `79dd0677` | `6fe38fdd-fc45-4d32-9221-5b7788ee51f2` |
| `Representation.CuspidalSupport.HarishChandraAssembly` | `ccad91d6` | `e28d3ffc-81b2-49c6-a66a-9a344a79e95a` |
| `Representation.CuspidalSupport.HarishChandraBoundaryProof` | `b63b3325` | `e28d3ffc-81b2-49c6-a66a-9a344a79e95a` |
| `Representation.CuspidalSupport.HarishChandraConverseProof` | `c9152dba` | `b7830d5b-ebb6-42e5-85f3-5b8f39a312d2` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | `a3d3a114` | `b605839f-d645-4427-892a-04dd871b7c49` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` | `908ea769` | `3201c31a-f357-4b17-abc2-e22fb1a8938a` |
| `Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` | `c0976267` | `2aacacad-31d0-47b4-9701-ac3865c0efbe` |
| `Representation.CuspidalSupport.LeviTensorFactorizationProof` | `cf3ee414` | `334e2222-c3e9-47e3-b05c-2afe12f49e94` |
| `Representation.CuspidalSupport.LeviTensorReflectionProof` | `60fde00b` | `0bd67a39-f7bb-49cd-a608-2521b22c6c42` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | `ea18e1f7` | `d042dc77-fd25-4c92-b943-d456ffd86fe9` |
| `Representation.CuspidalSupport.MinimalJacquetProof` | `dd0f42fe` | `f28607f5-1eef-4329-ae18-2576ef25ab6a` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | `6acd6deb` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` | `8c6610e7` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.ProperInductionProof` | `325eaa76` | `7b91ddfb-d311-47d0-9994-a5256dcdd85d` |
| `Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` | `78f65422` | `efbb43fc-b6ce-4376-8e50-96b28dd6f5a6` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` | `134889be` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | `c862f739` | `e1237fc1-de75-4a4d-924b-d509dc475361` |
| `Representation.CuspidalSupport.StandardJacquetComparisonProof` | `8101b5b6` | `e2c46108-7f86-4c0b-994d-3f34704b0261` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | `85ce2829` | `5becc159-1242-4fa4-9102-79aa6e2726c0` |
| `Representation.CuspidalSupport.ZeroRankEmbeddingProof` | `4211499e` | `d1684637-cf80-4266-8850-2d68c922d008` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` | `79bbad40` | `44f58b77-789a-478c-ba92-9e33b00c8a23` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | `c4c5439d` | `4e10058b-cc0b-4ad5-ae78-365562f533e7` |
| `Representation.Derivative.LeftMixedProductDerivativeProof` | `e99bbe1b` | `7e19f753-4515-4d87-9256-f366b6fc5683` |
| `Representation.Derivative.MirabolicDerivativeDetectionProof` | `3ace613e` | `ed056880-a4dc-4ebf-ad26-9878e508cf6c` |
| `Representation.Derivative.MirabolicHighestDerivativePairingProof` | `f957ae76` | `a925b519-9bb9-4927-873e-ad322d41328e` |
| `Representation.Derivative.MirabolicMinusExactnessProof` | `d307cd07` | `b65bc667-6951-4bd5-82af-10fb7046df7f` |
| `Representation.Derivative.MirabolicMinusPairingTransferProof` | `5715a6a0` | `96a1c747-9282-43a2-b8b7-d9180675f432` |
| `Representation.Derivative.MirabolicProductMinusBoundary` | `c8340e2a` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusLeftPhi` | `e32e2414` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusLeftPsi` | `8a6a0658` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightBoundary` | `58a3c341` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightPhi` | `5449db58` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightPsi` | `424f4227` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductRestriction` | `d58e34da`, `d8caeff4` | `a1d00661-0059-45f4-9f7c-3c6b3cf1af3a` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationProof` | `dbad7979` | `3231134e-a443-44f4-abda-39c3b5829f76` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` | `3e121bcb` | `c9dbd607-82e5-4821-b367-736e876565d9` |
| `Representation.Filtration.GradedRefinementProof` | `a6b9aa29` | `8f135e79-b688-4075-b8e6-b05a81a36883` |
| `Representation.Filtration.IntervalLiftProof` | `f47e01a0` | `58e0544d-0db2-42f5-8d39-79d38ff5e2cd` |
| `Representation.Filtration.IrreducibleMultiplicityProof` | `785e7c85` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.JordanHolderComparisonProof` | `93052369` | `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Representation.Filtration.JordanHolderProof` | `dac710c1` | `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Representation.Filtration.JordanHolderTransportProof` | `763c2ca6` | `77ffbd6e-17db-4751-8dee-c6dcb3b92e09` |
| `Representation.Filtration.LengthCriterionProof` | `6b07cbb0` | `8520a63d-88a5-45e7-adef-84849528ad9d` |
| `Representation.Filtration.LengthTwoMatching` | `701ca674` | `53969569-6b54-45b3-a1f8-89f1fe96a1f8` |
| `Representation.Filtration.MultiplicityAdditivityProof` | `fa942dbb` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof` | `ccd92a0c` | `0d7093cf-8a18-4d0f-ba5b-20b24b49f969` |
| `Representation.Filtration.MultiplicityIndependenceProof` | `619455f4` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.MultiplicityTransportProof` | `1905b374` | `b8ecf398-d8ff-48bd-a6b3-5da6557b7655` |
| `Representation.Filtration.QuasicuspidalVanishingProof` | `43dadb08` | `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Filtration.SimpleMapMultiplicityDetectionProof` | `f1afeb6f` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Filtration.SubquotientAlgebraProof` | `ff37b932` | `b605839f-d645-4427-892a-04dd871b7c49` |
| `Representation.Filtration.SubsingletonProof` | `37e5a059` | `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Filtration.ZeroFactorDeletionProof` | `2813cc17` | `e0f6a21c-44dd-4676-ad49-1656e49573ed` |
| `Representation.Geometric.BlockSixDecomposableProof` | `8e1b278f` | `91670dc7-3166-4d54-b9cb-bcb148f080b5` |
| `Representation.Geometric.BruhatMatrixExistenceProof` | `b5739893` | `f22fde8e-f597-44d0-a53d-290de4c59b2d` |
| `Representation.Geometric.BruhatWeylReflectionProof` | `9d034ed7` | `4ff454dd-caa9-435d-8c9b-bc4ed0d4b415` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | `ed2e1c45` | `e71f23b6-a9d9-4bc4-9af9-cde7a187ff8b` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | `0d68f886` | `9c98daee-a78a-429a-81dc-4cebbe02dee1` |
| `Representation.Geometric.GeometricLemmaProof` | `f606bb75` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | `8e3722a0` | `1a585c66-e21e-4071-84a0-09a32af9d745` |
| `Representation.Geometric.MonotoneBlocksProof` | `820f0b5d` | `a5db9be0-3f71-4528-89a8-cd92a0c5e411` |
| `Representation.Geometric.OrbitSectionExtensionProof` | `f6feecf9` | `58ca13a3-4bf3-4aaa-8b7d-e8156d189c64` |
| `Representation.Geometric.PadicCorrectionCancellationProof` | `54d42371` | `7e7f9c7b-a0fb-4b6a-9539-2d6b9988a4cc` |
| `Representation.Geometric.PadicParabolicBruhatProof` | `66197c1e` | `b2c9fb09-d2c7-4895-8320-b447e3cc98c6` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | `520b0e0b` | `18915f54-27ba-4ed6-a6ba-44d2590fd858` |
| `Representation.Geometric.ParabolicSupportGradedProof` | `62ae1acc` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.ParabolicSupportJacquetProof` | `b5caf4af` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.StandardIntersectionsProof` | `454f2f13` | `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | `be673197` | `6e35399b-9029-438e-9663-5ce96ab02576` |
| `Representation.Geometric.WeylUniquenessProof` | `1e54306f` | `9ad51693-f8a1-45de-949a-72d07ecc13b9` |
| `Representation.Hecke.CommonInvarianceProof` | `067a7f86` | `4b135fdc-c234-45a5-99ca-4730d3874d38` |
| `Representation.Induction.CharacterTwistProof` | `9709c7b6` | `fb3e71c3-36c9-4f69-bc65-3572eba2c084` |
| `Representation.Induction.CompactAutomorphismIntegralProof` | `822aed37` | `322d05be-f0c4-46f3-a5ce-0bb0a724e68f` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | `bd81652f` | `cbaf9d61-f090-41e3-8269-9ae5a6992693` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | `a9532713` | `9f55d4f4-ce37-42fa-881d-413bffce13e2` |
| `Representation.Induction.CompactLocalSectionSpanningProof` | `9dda760f` | `0dbbc4e6-1b6c-4682-9e94-bf4b9aa04614` |
| `Representation.Induction.CompactQuotientProof` | `53fcb4f0` | `672038be-3175-4fbd-85a6-d8c272aa63ec` |
| `Representation.Induction.CompactScalarProof` | `ceff0623` | `3d44eb6b-b164-4840-a276-23eef1b3f075` |
| `Representation.Induction.CompactSurjectivityProof` | `0f5c33e5` | `a757e2b6-b764-46f5-8f53-57f3d2d80f9b` |
| `Representation.Induction.CompactTransitivityProof` | `23261764` | `84a052cc-bc16-4936-b3c5-0e50f92ff0a8` |
| `Representation.Induction.FiniteProductTensorBijectiveProof` | `b8bead2c` | `907898cf-8008-4165-a299-db111d558d6f` |
| `Representation.Induction.NormalCoinvariantKernelProof` | `5b05899e` | `89c9c2dc-a112-4cae-b148-3e6de8be0583` |
| `Representation.Induction.NormalCoinvariantProof` | `9a15662a` | `ffe24f57-d375-48bf-b0ef-536f8cea58dd` |
| `Representation.Induction.OppositeProductReversalProof` | `2bdd098e` | `217bc764-94f7-4775-8b6c-eb96939cf3ba` |
| `Representation.Induction.SplitQuotientProof` | `e4355c7e` | `75bc696d-7093-45b4-b951-e84ca3cd5f79` |
| `Representation.Induction.SplitStagesCharacterComparison` | `0bf20b02` | `c4288181-e9d8-4ad2-961d-4d971b1fc625` |
| `Representation.Induction.SurjectivityProof` | `782edcc0` | `63c695c6-3dbd-46f6-b675-f46f1aa2a0bb` |
| `Representation.Jacquet.BlockCompressionProof` | `f43e70ce` | `5e1e7f7b-e604-43bc-abbb-983714e939eb` |
| `Representation.Jacquet.BlockPowerKernelProof` | `17fdf3cd` | `9036bb44-b05d-4c31-a1d2-b0ecc2471985` |
| `Representation.Jacquet.CanonicalLiftBijectivityProof` | `17f84643` | `faf28144-e82d-4543-8ad3-bfab5f2c89e2` |
| `Representation.Jacquet.CanonicalLiftGroupTransportProof` | `0dd3c75e` | `c6b0879c-008f-43a4-b961-7305495342c0` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof` | `fb7dc857` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.CompactCompressionStableDualityProof` | `c5db14dc` | `fcc707cc-1c32-43d4-a332-42e06ec288b0` |
| `Representation.Jacquet.CompressionStabilizationProof` | `f437baa7` | `d901e340-eb2c-46f2-ae8a-1e041c5dc1b4` |
| `Representation.Jacquet.ExactProof` | `a5d47bfd` | `d30fdbfc-1ea3-4554-9b0f-540abe813aea` |
| `Representation.Jacquet.LocalizationExactnessProof` | `ea6f8b30` | `0574c6f7-8717-4cb2-9498-46220d6b8048` |
| `Representation.Jacquet.OppositeCanonicalLiftProof` | `c28651b0` | `dbae9baf-759b-429d-a685-27521c0b454d` |
| `Representation.Jacquet.ReciprocityProof` | `35b48643` | `21341e99-4de8-4e83-967f-94131828a06d` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftProof` | `4e155df2` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositeCompressionProof` | `19663452` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositePowerKernelProof` | `5b5155c6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositeStableImageProof` | `655f10f8` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.MatrixCoefficient.NormRegularityProof` | `386e3eea` | `c98c74eb-a4cb-4924-8df8-f7556ca47689` |
| `Representation.Parabolic.InverseTransposeProductProof` | `96669dbb` | `fc1a5e69-5e8e-4fcd-ad69-c3d3d1384e91` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | `38c8bf1a` | `4c32a273-8e38-4a7c-abb9-f1ad5075ecb9` |
| `Representation.Parabolic.NaturalInductionDualityProof` | `ca3b908f` | `aca46f6c-3494-4a52-aeea-272a8b3fb5f1` |
| `Representation.Parabolic.NaturalJacquetDualityProof` | `67fa0cf2` | `48901b5f-7442-4471-bcb5-95578145d5d4` |
| `Representation.Parabolic.NormalizedAdmissibilityProof` | `c5fb6307` | `440ff377-ae50-452a-b26d-1587b3092538` |
| `Representation.Parabolic.NormalizedJacquetAdmissibilityProof` | `9104334f` | `98f79e48-f457-4ef6-ab80-7be0671d52b0` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | `eebdf376` | `9d580fe5-0589-4dfa-9506-1010e413a529` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityProof` | `7461d73d` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Parabolic.OppositeRefinementTransitivityProof` | `c9c6b113` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Parabolic.OrderedProductRegroupingProof` | `3c33bc41` | `2ef80e63-ce40-401c-8203-4cac37fb0307` |
| `Representation.Parabolic.QuotientCompactProof` | `6e7b4c94` | `400d2277-4574-4aea-a50c-da70cb1702f2` |
| `Representation.Parabolic.RefinedInductionTensorProof` | `91b8bcdb` | `fa77b238-a6a2-47ae-9847-87e6de1267de` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationProof` | `31344543` | `77267c3f-9c92-4929-951a-6e6892c89e64` |
| `Representation.Parabolic.RefinementInductionTransitivityProof` | `bce6cf35` | `05a83966-937f-4db1-9195-8ec40311fccd` |
| `Representation.Parabolic.SecondAdjointnessProof` | `4be76e11` | `eb76bbde-911c-4875-9611-a11b9ba0300e` |
| `Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof` | `f3f923d0` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Parabolic.UnipotentFiniteContainment` | `bf7f18d2` | `cba1f5ba-df9a-4ee7-a403-baaeebbf4d63` |
| `Representation.RankinSelberg.EqualRankFrobeniusProof` | `1746c825` | `101089c8-6e44-4d3f-b2bf-390f3dc96aff` |
| `Representation.RankinSelberg.GeneralLinearUnimodularity` | `0a2f2e5a` | `0eb4a44f-89d4-473a-bf4f-a7cf2dcaaf9d` |
| `Representation.RankinSelberg.HaarSymmetriesProof` | `b0680b80` | `25af224a-861b-48d6-9a6f-76284babdde5` |
| `Representation.RankinSelberg.LastRowCompactOrbitProof` | `705eefa7` | `8f82e3a6-5ccb-4c0b-b68a-c0e6550c8f4a` |
| `Representation.RankinSelberg.UnipotentUnimodularity` | `e5699c5d` | `4ad92be9-9115-4e7d-b42a-b2adc7dde3e5` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | `c1ca32b0` | `06486d65-100f-4e95-b759-bb94e5ff8a98` |
| `Representation.Schur.CountableDimensionProof` | `22a3240d` | `adb98036-1da4-480f-8bac-a97f8173aa1f` |
| `Representation.Smooth.Contragredient.AdmissibleDualityProof` | `81c91e2f` | `a7dd454e-3648-46fd-99db-2029b21d38bb` |
| `Representation.Smooth.Contragredient.ExactProof` | `ed74312b` | `41755c34-9780-45df-88a4-3a7ccd32727e` |
| `Representation.Smooth.Contragredient.GelfandKazhdanProof` | `31571ec8` | `2206daa6-e219-4ed6-9ad1-4f4d47efed93` |
| `Representation.Smooth.Contragredient.HomDualityProof` | `a45dfb51` | `2df2312f-ac71-4f1a-bacb-d4ef2b0d741f` |
| `Representation.Smooth.Contragredient.InvariantPairingProof` | `4e0757e6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Smooth.Factorization.TwoFactorExistenceProof` | `1470f0d7` | `ea7e032e-0818-4425-9fc4-6f30126f4fc4` |
| `Representation.Smooth.FixedVectors.FiniteTypes` | `2318628c` | `ea272d1e-81f4-4c94-9c95-0dd6fa13d02f` |
| `Representation.Smooth.FixedVectors.GenerationInheritance` | `4065bf79` | `6746614f-7462-4b18-a9e6-07824468d9d8` |
| `Representation.Smooth.Schur.Proof` | `b97b88e5` | `7418b301-258f-4839-83ff-8b508b8a9abd` |
| `Representation.Smooth.SmallRealizationProof` | `b9fc82a3` | `baca19e0-4b51-4368-9b1a-817f6d583c5f` |
| `Representation.Tensor.ExternalMapSurjectivityProof` | `e485a89c` | `c1dbdd67-682c-4d5d-ba6b-43eb6850899b` |
| `Representation.Tensor.SmoothDualInjectivityProof` | `c179611a` | `de802971-5655-401f-a4e8-55e4638699af` |
| `Representation.Tensor.SmoothDualSurjectivityProof` | `b9cdbe70` | `7ad0562a-0aa8-43a6-afcd-6934200e7488` |
| `Representation.Tensor.UnitaryProof` | `373fa4ed` | `f3a2dc88-79d8-4ecf-aaf1-2125d4479a2d` |
| `Representation.Twist.AdmissibilityProof` | `4d0e0b40` | `481101cd-15e1-460d-84f8-3bc4331be8b6` |
| `Representation.Twist.SubquotientProof` | `2b2f7961` | `84b8a0ef-a7b9-4ed9-ab40-1b430d7e0f86` |
| `Representation.Unitary.CentralCharacterProof` | `a1b935a6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationProof` | `7fbc2ac8` | `f5b075b2-71a6-407d-8916-4de3b0e9df58` |
| `Representation.Unitary.SquareIntegrableProof` | `5cfbe4bb` | `1559297e-fc4f-49fc-bc37-b7c577c2ba15` |
| `Representation.Unitary.SupercuspidalRealUnitarizationProof` | `ad033912` | `733b7c5a-b9dc-4400-b830-0b91eaadf062` |
| `Representation.Unitary.UnitarizabilityContinuationProof` | `ec26db35` | `7071b052-61cb-4718-babc-684a3e41c288` |
| `Representation.Unramified.SphericalConstituentExistenceProof` | `1ff36e36` | `e2e8da65-f92d-44fa-ac52-7c07e4290054` |
| `Representation.Whittaker.BruhatCellFactorizationProof` | `01bfb9b7` | `c2b0bc2a-c78e-4b75-a659-fee05f37a288` |
| `Representation.Whittaker.BruhatCellInvarianceProof` | `4c108f89` | `40ca3d44-8e3a-40d4-9118-16fcac627174` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingProof` | `2654bbe6` | `db3fb63c-73d8-4983-ae3b-e78a50893941` |
| `Representation.Whittaker.BruhatCellVanishingProof` | `6c2d19dc` | `2c904012-21c7-4439-ac2f-4f6a7e10893d` |
| `Representation.Whittaker.BruhatCompatibleSupportProof` | `591b752d` | `49e92410-96d1-4d78-987c-d3ad6fb6d31b` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceProof` | `21eb8285` | `74e1dd97-9e58-4212-bcb9-310b35fa3ae3` |
| `Representation.Whittaker.BruhatHaarMeasureProof` | `e9717f96` | `22bc586a-014c-4a50-be9e-bb696f270907` |
| `Representation.Whittaker.BruhatOrbitalIntegrationProof` | `df367457` | `b983acdc-4624-46e6-9453-91a2ceb6bab7` |
| `Representation.Whittaker.CompatibleMonomialFixedProof` | `6e7d99cc` | `262fa24b-c35c-4b90-9e7c-753c3ab85316` |
| `Representation.Whittaker.DistributionInvarianceProof` | `1ffc4346` | `f79ca82c-d050-4ffa-821b-c347b60e36e0` |
| `Representation.Whittaker.GeneralizedCoefficientKernelProof` | `bcf252a5` | `2509ba9f-84e5-486f-b995-7a800b413390` |
| `Representation.Whittaker.MultiplicityOneProof` | `ba2dff22` | `209cde88-bab8-4a85-8a9d-72b8864b6fa0` |
| `Topology.GroupAction.FiniteOrbitProof` | `d152e80f` | `72152240-c606-4fc3-87a0-e6d5972c32fa` |
| `Weil.Representation.ContinuityProof` | `d1c7c679` | `8d52aad7-9f5b-41c1-bf76-c1e6483b9639` |
| `Weil.Representation.IsomorphismInvarianceProof` | `a36e26ca` | `53bd2d23-f25a-4747-9ac9-f82617e20070` |
| `Weil.Representation.OperationClosureProof` | `a6debf58` | `4fa46ac6-ab54-44b7-ab47-ddaa64fbb061` |

The second table lists the 30 further closure modules that prove a named
Library proposition but are not the entry module of a current proof record. It
includes every remaining closure module whose name ends in `Proof`. They come
from the project's first proof rounds, or they are helper modules shipped with
a later proof. "Historical" marks a module that has no proof task in the
current task registry. For such a module the table gives the published
statement and any task that its Markdown names. Twenty-nine of these rows lie
in the closure of the S1 proof and repeat the S1 proof's audit. The row
`ConstituentRankZero` was added for the modules outside that closure.

| Proved module | Provenance |
| --- | --- |
| `Galois.FiniteField.ComparisonProof` | historical; proves `FrobeniusComparison` (module `Galois.FiniteField.Comparison`); imported by `Weil.Local.Assembly` (supporting unit `3b435643`, task `650de61a-84c3-40d1-b791-0544af5824e1`) |
| `Galois.Local.SpectralProof` | historical; statement artifact `c9ec9a6a-5b72-444a-bfb0-7c5406d5950d` (`SpectralResidueExactness`), proof task `f0e0e8d0-9bed-439a-a648-f7d8d9939d3b` named in its Markdown |
| `Group.GL.Nonarchimedean` | historical; statement module `Group.GL.NonarchimedeanStatement` (`ValuativeGeneralLinearNonarchimedean`) |
| `LocalField.Normalization.Proof` | historical; statement artifact `62e8bb5c-3f54-449e-bbd6-98de9dc15781` (`PadicNormalizationStatement`) |
| `Representation.Compact.ProjectionProof` | historical; statement artifact `91124244-2c99-4f10-91d2-bcab3a34712c`, proof task `849a1dbe-68d3-4bc8-9c67-ca059539e827` named in its Markdown |
| `Representation.Compact.SurjectivityProof` | historical; statement artifact `40e87eae-9077-41b0-a7d0-49e3f58c1d41` |
| `Representation.CuspidalSupport.ConstituentRankZero` | proves the rank-zero case `leviCuspidalConstituent_rankZero` of `LeviCuspidalConstituentTheorem`; helper of `CuspidalSupport.ConstituentProof` (proof `00a93329`, task `fe734e49`), which uses it for rank zero |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` | proves `DeterminantUnitCornerStructureStatement` (BZ76 Lemma 4.9); helper of `CuspidalSupport.CompactCoefficientFinitenessProof` (proof `a23cbcdb`, task `6884361c-0ab2-41b3-8098-9c070c4a1b3e`) |
| `Representation.CuspidalSupport.HarishChandraForwardProof` | helper of `CuspidalSupport.HarishChandraAssembly` (proof `ccad91d6`, task `e28d3ffc-81b2-49c6-a66a-9a344a79e95a`); its theorems take the Cartan decomposition as a hypothesis, which the assembly discharges |
| `Representation.Jacquet.RefinedUpperCanonicalLiftProof` | helper of `Parabolic.NaturalJacquetDualityProof` (proof `67fa0cf2`, task `48901b5f-7442-4471-bcb5-95578145d5d4`); adds no statement |
| `Representation.Jacquet.StablePairingProof` | helper of `Parabolic.NaturalJacquetDualityProof` (same task); adds no statement |
| `Representation.MatrixCoefficient.LawsProof` | historical; statement artifact `e850d833-de95-42c7-acbd-29cdfcad52e7`, task `d472d77b-c3d3-42a4-9ff3-d8acbb94a2d7` named in its Markdown |
| `Representation.Smooth.Admissibility.CofinalProof` | historical; statement artifact `accbe6c3-27d4-43d9-a227-65c4e7b6a993` |
| `Representation.Smooth.Admissibility.EmbeddingProof` | historical; statement artifact `e95c3f58-3ed4-4ddc-b666-462d05ec8cca` (`AdmissibleSubrepresentationStatement`) |
| `Representation.Smooth.Admissibility.EquivalenceProof` | historical; statement artifact `b844a6ce-e7d4-4e71-8bd3-8a80abb57ba0` |
| `Representation.Smooth.Contragredient.CompactDualityProof` | historical; statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | historical; statement artifact `ff1e06de-a5b0-4bc7-81b5-8b4555029cef` |
| `Representation.Smooth.FixedVectors.LawsProof` | historical; statement artifact `d720bdcb-b2b8-4bf6-9b86-31702bea43e6` |
| `Representation.Smooth.FixedVectors.OrderProof` | historical; statement artifact `81e1f095-d4a9-4b4c-ae57-d746ec2fb206` |
| `Representation.Smooth.SmoothPart.BasicProof` | historical; statement artifact `7101568f-3e71-4b9d-b1c5-f35546e0e8dd`, task `3b5e1c81-ba5a-4300-8ff6-27a11ca276e7` named in its Markdown |
| `Representation.Smooth.Transfer.PullbackProof` | historical; statement artifact `f7707f55-9abd-49f4-98e3-d7629f206ee1`, proof task `442dfa1c-e218-4bd4-b7c0-faaccfcf26e7` named in its Markdown |
| `Representation.Smooth.Transfer.SubquotientProof` | historical; statement artifact `b838525e-4b0b-4f85-9085-6f384abedf7a`, proof task `0975ce00-a7a0-4031-a31f-1df98f3afaf3` named in its Markdown |
| `Representation.Twist.AlgebraProof` | historical; statement artifact `2fbcd8fa-9374-4793-bf3b-f0e5a4fbb3d7` |
| `Representation.Twist.ContinuousCharacterProof` | historical; statement artifact `f56acc86-4146-4652-ace8-72cda7a39b7f` (`ContinuousComplexCharacterOpenKernel`), proof task `745f8453-6791-4cc3-91e0-afaf64adb387` named in its Markdown |
| `Representation.Twist.DualProof` | historical; statement artifact `5c831314-e615-411f-9218-bc54346cef78` |
| `Representation.Twist.PullbackProof` | historical; statement artifact `68b9e381-f850-446e-9fa9-4dd178f19481` |
| `Representation.Twist.SmoothProof` | historical; statement artifact `f3828b8f-ac55-4352-955b-9dc9787da742` (`TwistSmoothCompatibility`) |
| `Topology.CompactOpen.NeighborhoodBasis` | historical; statement artifact `25905329-f69e-4866-b0e7-97673395dd3b`, proof task `83c9e2e3-7d24-4ae8-ba36-8fda72b4f789` named in its Markdown |
| `Weil.AlgebraicProof` | historical; statement artifact `a1ca17e7-e6e7-40de-866f-a1db719cc6a2` |
| `Weil.TopologyProof` | historical; statement artifact `9e116c5c-4503-4f92-8dec-62ce6615b117` |

None of the IDs in the second table is among the exclusions. To find these
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
  and `Classification.SegmentSocleDecreasingHead` (Worker 167, this task). They
  assume `SegmentZelevinskyConstituentExistence`, which
  `JuxtaposedConditionalAssembly` supplies as the published
  `segmentZelevinskyConstituentExistence`;
- `CuspidalSupport.AssociationForwardHomSupport` (Worker 240). It assumes
  `LeviCuspidalConstituentTheorem`, which its user
  `CuspidalSupport.AssociationForwardHomProof` (proof `0b61f195`, task
  `18476e24`) supplies as the published `leviCuspidalConstituentTheorem`;
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

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library
commit `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` built this module and its
fourteen helper modules with no errors or warnings. Inspection of
`Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure`
reports a theorem with level parameters `uF, uV` and the axioms `propext`,
`Classical.choice` and `Quot.sound` only.
