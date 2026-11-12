# Proof of the chamber-conjugate intersection

Author: Worker 4691.

This unit proves the published target
`Langlands.Geometry.Building.ChamberConjugateIntersectionStatement` of
`Langlands/Geometry/Building/AffineIwahoriTitsInputStatements.lean`. The theorem
`Langlands.Geometry.Building.chamberConjugateIntersection` is stated at an arbitrary
universe `u`. Its type is exactly `ChamberConjugateIntersectionStatement.{u}`, so no
hypothesis is changed or added. The target's Lean/Markdown pair is unchanged.

## What is proved

The target is the saturation step of the proof of KP Theorem 7.5.1,
`⋂_{n ∈ N} n I n⁻¹ = Z`, stated directly on `G(F)^0`. It quantifies over every
nonarchimedean local field `F`, every group scheme `G` over `Spec F` with
`[IsAffineHom G.X.hom]`, and every `P : ParahoricBuildingData G` satisfying
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. For every chamber `C` of
`P.affineRoots` and every `g : rationalPoints G`, it says: if
`g ∈ P.parahoric (n • C)` for every `n : normalizerPoints P.i` with
`(n : rationalPoints G) ∈ P.zeroSubgroup`, then
`g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j)`.
In the notation of the target module, an element of `P_{n C}` for every
`n ∈ N(F) ∩ G(F)^0` lies in `Z(F)^0`.

## The implemented proof

The final step applies the published conditional theorem
`ParahoricBuildingData.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent`
(module `ChamberParahoricIntersection`). Its conclusion and its premise on `g` are the
target's, with the same quantifier over normalizer points in `P.zeroSubgroup`. The
Markdown of that module describes its argument: a generic cocharacter and the full
chamber decomposition write `g` as a negative unipotent factor, a `Z(F)^0` factor and a
positive unipotent factor. Every affine Weyl transformation is realized by a point of
`N(F) ∩ G(F)^0`. At each affine Weyl translate of `C` the published three-factor
injectivity `unipotentTripleProduct_injective` identifies the unipotent factors, and a
reflection argument on root valuations shows that they are trivial.

That theorem has four premises besides the target's own hypotheses. Each is discharged
here from published results:

1. `P.apartment.SatisfiesApartmentAxioms P.centralizer` is the target's hypothesis.
2. `RelativeRoot.HasRankOneFactorization P.i` is the published
   `rootRankOneFactorization` applied to `F`, `G`, `P.isConnectedReductive`, `P.S`, `P.i`
   and `P.isMaximalSplitTorus`.
3. `RelativeRoot.DynamicRootOrderedProductStatement` is the published
   `RelativeRoot.dynamicRootOrderedProduct`.
4. `P.ChamberIwahoriDecompositionStatement` comes from the published
   `chamberIwahoriPrerequisiteReduction`. Its inputs are the two published proofs just
   named and the centralizer intersection `P.CentralizerParahoricIntersectionStatement`
   (KP Lemma 7.4.3). That intersection is the published
   `ParahoricBuildingData.centralizerParahoricIntersection_of_rankOneFactorization`,
   applied to item 2 and to the cover-image containment
   `P.zeroDatum.CoverImageCentralizerNormKernelStatement` proved below.

### Supporting theorems in this module

Five auxiliary theorems supply the cover-image containment. Each is a composition of
published proofs with published conditional theorems; none adds a hypothesis.

- `isSimplyConnectedAlgebraicClosureAscent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u}`.
  Simple connectedness is preserved by base change to an algebraic closure. This is the
  published `isSimplyConnectedFieldExtension` at `K = AlgebraicClosure k`; the base-change
  map `toAlgebraicClosure k` is by definition
  `Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))`.
- `splitTorusCentralizerDerivedSimplyConnected : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u}`.
  In a simply connected group, the derived subgroup of the centralizer of a split
  subtorus is simply connected. This is the published
  `splitTorusCentralizerDerivedSimplyConnected_of_inputs`, applied to the published
  `dynamicCentralizerReductive`, `derivedSubgroupSemisimple`,
  `splitSimplyConnectedCorootSpan`, `splitCorootSpanSimplyConnected`,
  `splitTorusCentralizerDerivedCorootComparison` and the preceding theorem.
- `splitTorusCentralizerCoverPreimage : SplitTorusCentralizerCoverPreimageStatement.{u}`.
  The preimage of a split-torus centralizer in a simply connected cover of the derived
  subgroup, with the properties listed in that statement. This is the published
  `splitTorusCentralizerCoverPreimage_of_inputs`, applied to the published
  `reductiveCentralDerivedProduct`, `dynamicCentralizerReductive` and the preceding
  theorem.
- `splitTorusCentralizerCocenterInduced : SplitTorusCentralizerCocenterInducedStatement.{u}`.
  In a simply connected group, every commutative fppf quotient of a split-torus
  centralizer by its derived subgroup is an induced torus. This is the published
  `splitTorusCentralizerCocenterInduced_of_inputs`, applied to the bundle of the published
  `dynamicCentralizerReductive`, `cocenterQuotientExistence`,
  `isSimplyConnectedFieldExtension`, `splitSimplyConnectedCorootSpan` and
  `splitTorusCentralizerCocenterRootModel`.
- `ZeroSubgroupDatum.coverImageCentralizerNormKernel`: for every actual zero datum
  `E : ZeroSubgroupDatum i j` over a nonarchimedean local field,
  `E.CoverImageCentralizerNormKernelStatement`, that is,
  `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` (the cover-image containment in the proof of KP
  Corollary 2.6.28). This is the published `coverImageCentralizerNormKernel_of_inputs`,
  applied to the published `cocenterQuotientExistence`, the cocenter theorem above, the
  published `inducedTorusIwahori`, the cover-preimage theorem above and the published
  `isSimplyConnectedFieldExtension`.

The development check of this module reported no errors or warnings. The axioms of
`chamberConjugateIntersection` are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The target is the saturation step of KP Theorem 7.5.1 (Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, 2023, printed pp. 259–260 / PDF pp. 290–291), with the
1 November 2024 corrections (PDF p. 35) replacing `⋂_{n ∈ N} I` by `⋂_{n ∈ N} n I n⁻¹`.
The target module's Markdown explains why it is stated on `G(F)^0` with `P_{n C}`. KP's
proof says only that the argument for `I ∩ sIs ≠ I` "can be iterated". The implemented
route is the published Library argument summarized above. It uses KP Lemma 7.4.3 and
the cover-image step of KP Corollary 2.6.28 through their published Library forms.

This unit is conditional only in the sense of the target: it is a theorem about supplied
`ParahoricBuildingData` satisfying the fixed-apartment axioms. It does not construct such
data, and it does not prove the other inputs of `AffineIwahoriTitsStatement`.
