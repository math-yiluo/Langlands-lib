# Integral coroot generation from explicit root-cell and root-line inputs

This module gives a derived, conditional reduction of
`SplitSimplyConnectedCorootSpanStatement` (module
`Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement`). The target
follows from three published propositions, which enter only as explicit
hypotheses:

- `RootDatumExistenceStatement`
  (`Langlands.GroupScheme.Reductive.RootDatumStatement`);
- `SplitRankOneRootCellStatement`
  (`Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement`);
- `SplitRootLieLineStatement`
  (`Langlands.GroupScheme.Reductive.SplitRootLieLineStatement`).

The module proves none of the three, so it does not prove
`SplitSimplyConnectedCorootSpanStatement` itself. The point of the module is
which inputs it uses. Its theorems do not use the Library proofs
`rootDatumExistence`, `splitRankOneRootCell`, `splitRootLieLine` or
`rootLieLine_of_dynamicCentralizerReductive`, nor the dynamic-Borel and
projective-Borel results behind them (see the audit below). Once the three
statements have independent proofs, `splitSimplyConnectedCorootSpan_of_corootSpanLineInputs`
applied to them is such a proof of the target.

## Definitions

`SplitCorootSpanLineInputs.{u}` is the conjunction, at one arbitrary universe
`u`, of `RootDatumExistenceStatement.{u}`, `SplitRankOneRootCellStatement.{u}`
and `SplitRootLieLineStatement.{u}`, in this order. It bundles these three
statements and adds no hypothesis of its own. In words:

- `RootDatumExistenceStatement`: for every field `k`, connected reductive `G`
  over `Spec k`, split commutative torus `T` and maximal torus
  `i : T.toGrp ⟶ G`, there are a finite index type `J` and a reduced root
  datum `P` on the character and cocharacter lattices of `T` with
  `IsRootDatumOf i P`. Milne, *Algebraic Groups*, Theorem 21.11, split case.
- `SplitRankOneRootCellStatement`: in a connected reductive `G` over a field
  with split maximal torus `i` and root datum `P` of `i`, if no two roots are
  linearly independent over `ℤ`, then each root `P.root r` has root groups
  `xp`, `xm` from `𝔾ₐ`, on which the torus acts through `±P.root r`. The map
  `(Y, t, X) ↦ xm(Y) t xp(X)` is an open immersion. The product `xp(X) xm(Y)`
  lies in its image exactly when `u = 1 + XY` is a unit, and then
  `xp(X) xm(Y) = xm(u⁻¹Y) (P.coroot r)(u) xp(u⁻¹X)`. Conrad, *Reductive group
  schemes*, Theorem 4.1.4, Remark 4.2.4 and Theorem 4.2.6.
- `SplitRootLieLineStatement`: in a connected reductive `G` over a field with
  split maximal torus `i`, the Lie-algebra weight space `weightSpace i χ` of
  every root `χ ∈ roots i` is one-dimensional, as
  `Nonempty (k ≃ₗ[k] weightSpace i χ)`. Milne Theorem 21.11(b).

The exact Lean statements and their sources are in the paired Markdown of the
three statement modules.

## Main results

`splitSimplyConnectedCorootSpan_of_corootSpanLineInputs (h : SplitCorootSpanLineInputs.{u})`
proves `SplitSimplyConnectedCorootSpanStatement.{u}`, with that statement
unchanged as the conclusion. For every field `k : Type u`, algebraically simply
connected `G` over `Spec k`, split commutative torus `T`, maximal torus
`i : T.toGrp ⟶ G`, finite index type `J : Type u` and root datum `P` of `i`
with `IsRootDatumOf i P` and `P.IsReduced`, it gives `P.corootSpan ℤ = ⊤`.

Two intermediate theorems are stated separately:

- `splitCentralIsogenyExistence_of_corootSpanLineInputs (h : SplitCorootSpanLineInputs.{u})`
  proves `SplitCentralIsogenyExistenceStatement.{u}`, the existence half of the
  central Isogeny Theorem (Milne Theorem 23.9). Let `G`, `G'` be connected
  reductive groups with split maximal tori `i : T.toGrp ⟶ G`,
  `i' : T'.toGrp ⟶ G'` and root data `P`, `P'`. A morphism of root data
  `f : P' ⟶ P` with injective weight and coweight maps comes from a central
  isogeny `φ : G ⟶ G'` and a torus homomorphism `t : T ⟶ T'` with
  `i ≫ φ = t ≫ i'`, and the weight map of `f` is pullback of characters along
  `t`.
- `splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine (hCell : SplitRankOneRootCellStatement.{u}) (hLine : SplitRootLieLineStatement.{u})`
  proves `SplitCommonTorusIsomorphismStatement.{u}`, the Isomorphism Theorem
  for a common split maximal torus (Milne Theorem 23.25 with Remark 23.26). Let
  `G₁`, `G₂` be connected reductive with maximal tori `i₁`, `i₂` of a split
  torus `T`, and let `P₁`, `P₂` be root data of `i₁`, `i₂` whose roots and
  coroots match under a reindexing `e : J₁ ≃ J₂`. Then there is an isomorphism
  `ψ : G₁ ≅ G₂` with `i₁ ≫ ψ.hom = i₂`. This theorem does not use root-datum
  existence.

## Supporting declarations

These are in namespace `Langlands.GroupScheme.LeviGluing`. They are copies of
`SimpleComparisonGraph.weightKernelTrivial_of_orthogonal`,
`SimpleComparisonGraph.weightKernelTrivial` and
`algClosedGraphProjectionIsomorphisms` from
`Langlands.GroupScheme.Reductive.SplitLeviGluingFactorInjectivity`. There is one
change: the root-line fact for the graph group comes from the explicit
hypothesis `hLine : SplitRootLieLineStatement.{u}`, where the originals call
`rootLieLine_of_dynamicCentralizerReductive`.

- `SimpleComparisonGraph.weightKernelTrivial_of_orthogonal_of_rootLieLine`.
  Hypotheses: `hLine`; `D : SimpleComparisonGraph i₁ i₂` for tori
  `i₁ : T.toGrp ⟶ G₁`, `i₂ : T.toGrp ⟶ G₂`, with `G₁`, `G₂` affine over `Spec k`;
  `hG₁ : IsConnectedReductive G₁`; `hmax₁ : IsMaximalTorus i₁`;
  `hroots : roots i₁ = roots i₂`;
  `hH : IsConnectedReductive D.envelope.group`;
  `htmax : IsMaximalTorus D.envelope.torusLift`; a homomorphism
  `p : D.envelope.group ⟶ G` to an affine `G`; a simple index `a`, with
  `D.envelope.localLift a ≫ p` a monomorphism; a character `χ ≠ 0` with
  `latticePairing T χ (D.directions.direction a) = 0`. Conclusion:
  `WeightKernelTrivial p D.envelope.torusLift χ`, i.e. the differential of `p`
  kills no nonzero vector of the `χ`-weight space of the graph group. Unlike the
  original, it has no `[IsAlgClosed k]` hypothesis. The original used that
  hypothesis only to call `rootLieLine_of_dynamicCentralizerReductive`.
- `SimpleComparisonGraph.weightKernelTrivial_of_rootLieLine`. Hypotheses:
  `hLine`; `D`; `E : D.GraphDynamicFactors`; `hG₁`; `hmax₁`; a root datum `P₁`
  of `i₁` (`hP₁ : IsRootDatumOf i₁ P₁`, any index type); `hroots`; `hH`;
  `htmax`; `p : D.envelope.group ⟶ G` with `G` affine and
  `ht : D.envelope.torusLift ≫ p = i`, where `i.hom.hom` is a monomorphism;
  `hmono`: every `D.envelope.localLift a ≫ p` is a monomorphism. Conclusion:
  `WeightKernelTrivial p D.envelope.torusLift χ` for every character `χ`. It
  has no `[IsAlgClosed k]` hypothesis either.
- `algClosedGraphProjectionIsomorphisms_of_rootLieLine (hLine)` proves
  `AlgClosedGraphProjectionIsomorphisms.{u}`
  (`Langlands.GroupScheme.Reductive.SplitLeviGluingDescent`). Over an
  algebraically closed field `k`, let `G₁`, `G₂` be connected reductive with
  maximal tori `i₁ : T.toGrp ⟶ G₁`, `i₂ : T.toGrp ⟶ G₂` of a common torus `T`,
  root data `P₁`, `P₂` of `i₁`, `i₂`, and `roots i₁ = roots i₂`. Then both
  projections `D.envelope.first` and `D.envelope.second` of every
  `D : SimpleComparisonGraph i₁ i₂` are isomorphisms. The graph data include
  splitness of `T` (`D.split`).

## Proofs

`weightKernelTrivial_of_orthogonal_of_rootLieLine`. If `χ` is not a root of the
graph torus, `weightKernelTrivial_of_not_mem_roots` applies. Otherwise `χ` is a
root of `i₁` (`D.roots_subset_first`). The local Levi `left` of `a` is connected
reductive (`dynamicCentralizerReductive`). Its roots are the roots of `i₁`
pairing to zero with `direction a` (`dynamicCentralizerRoots`), so `χ` is one of
them, and `left` has a nonzero vector `Y` of weight `χ`. Its image `X₀` under
the differential of `localLift a` has weight `χ` for the graph torus
(`leftTorus_localLift`). The differential of `localLift a ≫ p` is injective
because that map is a monomorphism (`Lie.targetMapLinear_injective`), so the
differential of `p` does not kill `X₀`. Now `hLine`, applied to the graph group
(`hH`), the split torus `T` (`D.split`) and the maximal torus
`D.envelope.torusLift` (`htmax`), shows that the `χ`-weight space is a line.
`weightKernelTrivial_of_finrank_eq_one` concludes.

`weightKernelTrivial_of_rootLieLine`. The proof is the original one with the
lemma above in place of `weightKernelTrivial_of_orthogonal`. The zero weight
uses `weightKernelTrivial_zero` and the self-centralizing graph torus
(`E.torus_selfCentralizing`). Nonzero non-roots use
`weightKernelTrivial_of_not_mem_roots`. For roots, `positive_induction`
(`SplitLeviGluingSimpleGeneration`) is applied to the property "trivial kernel
at `ψ` and at `-ψ`". At a simple root `a`, the characters `±a` and `±2 • a` are
nonzero and orthogonal to `direction a` (`D.directions.annihilates`), so the
lemma above gives the property there. The property is stable under simple
reflections by the Library's `weightKernelTrivial_reflection`. A root `χ` of the
graph torus pairs nonzero with the generic chamber (`D.directions.generic`), and
the property at whichever of `χ`, `-χ` is positive gives the claim.

`algClosedGraphProjectionIsomorphisms_of_rootLieLine`. The proof is the
original one with `weightKernelTrivial_of_rootLieLine hLine` in place of
`weightKernelTrivial`. With `E = D.graphDynamicFactorsOfReductive`
and `F = D.graphFactorProjectionsOfReductive`, the graph group is connected
reductive (`D.isConnectedReductive`) with maximal torus
`D.envelope.torusLift` (`E.isMaximalTorus`). For `p = first` and
`p = second`, the composites with the local lifts are monomorphisms:
`leftInclusion`, resp. `iso.hom ≫ rightInclusion`. So both differentials are
injective (`targetMapLinear_injective_of_weightKernelTrivial`). Then
`UnipotentProjectionData.isIso_of_lieKernel` makes the four unipotent factor
maps isomorphisms, and `E.isIso_first_of_factorIsomorphisms` and
`E.isIso_second_of_factorIsomorphisms` make both projections isomorphisms.

`splitCommonTorusIsomorphism_of_rootCell_of_rootLieLine`. The Library's
reduction `splitCommonTorusIsomorphism_of_rankOne_of_leviGluing` takes two
inputs. The rank-one Isomorphism Theorem is
`splitRankOneCommonTorusIsomorphism_of_rootCell hCell`
(`SplitRankOneRootCellReduction`). The gluing step is
`LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs` (`SplitLeviGluingDescent`,
descent from an algebraic closure), applied to
`algClosedGraphProjectionIsomorphisms_of_rootLieLine hLine`.

`splitCentralIsogenyExistence_of_corootSpanLineInputs`. The Library's reduction
`splitCentralIsogenyExistence_of_commonTorusIsomorphism`
(`SplitCentralIsogenyReduction`) is applied to four inputs: `h.1`
(root-datum existence, for the root datum of the central quotient), the
published `centralIsogenyRootDatumHom` and `splitCentralTorusQuotient`, and the
Isomorphism Theorem above, built from `h.2.1` and `h.2.2`.

`splitSimplyConnectedCorootSpan_of_corootSpanLineInputs`. The Library's
conditional assembly `splitSimplyConnectedCorootSpan_of_inputs`
(`SplitNecessityAssembly`) is applied to the published Existence Theorem
`splitReductiveExistence`, the central Isogeny Theorem above, and the published
semisimplicity criterion `splitSemisimpleRootDatum`. That assembly follows the
converse half of Milne Proposition 23.59. The coroots of `P` span a sublattice
of finite index, since `G` is semisimple. The split group `C` with the simply
connected root datum of `P` maps to `G` by a central isogeny realizing the
inclusion of root data. Simple connectedness of `G` makes this isogeny and its
torus map isomorphisms, so the coroot span is the whole cocharacter lattice.

## Independence audit

A private type-and-value closure scan was run over the compiled environment.
It follows every constant in the type and the value of every reached constant
and treats excluded constants as leaves. The excluded names, all in namespace
`Langlands.GroupScheme`, were: `parabolicDynamic`, `regularCocharacterBorel`,
`rankOneSolvableObstruction`, `rankOneBorelDynamic`,
`rankOnePositiveRootUniqueness` and their five statements; `rootDatumExistence`,
`rootReducedness`, `splitRankOneRootCell`, `splitRootLieLine`,
`rootLieLine_of_dynamicCentralizerReductive`,
`rootLieLine_of_twoStructuralInputs`,
`absoluteRootTangent_le_one_of_structuralInputs`,
`prescribedBorelProjectiveCurveData`,
`HomogeneousQuotient.regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`,
`reductiveGeometricReductivity`, `steinbergBigCell`, `absoluteBruhatCovering`
and `isParabolicSubgroup_of_range_eq_dynamicParabolic`.

Results:

- The closure of `splitSimplyConnectedCorootSpan_of_corootSpanLineInputs`
  (117,620 constants, 23,695 in `Langlands`) reaches none of these names. It
  also reaches no constant declared in the 18 modules that hold them:
  `Absolute.ParabolicDynamicProof`, `Absolute.RegularCocharacterBorelProof`,
  `Absolute.RankOneSolvableProof`, `Reductive.RankOneBorelDynamicProof`,
  `Reductive.RankOnePositiveRootProof`, `Reductive.GeometricReductivityProof`,
  `Reductive.RootDatumExistence`, `Reductive.RootReducednessProof`,
  `Reductive.SplitRankOneRootCellProof`, `Reductive.SplitRootLieLineProof`,
  `Reductive.RootLieLineFromTangent`,
  `Absolute.RootVectorLineStructuralAssembly`,
  `Reductive.RankOneProjectiveBorelAssembly`,
  `Reductive.RankOneCurveCentralizerProof`,
  `Reductive.RootTangentCurveDimension`, `Reductive.SteinbergBigCellProof`,
  `Absolute.BruhatCoveringProof` and `Absolute.DynamicParabolicRecognition`.
- The same holds separately for each component: `splitReductiveExistence`,
  `splitSemisimpleRootDatum`, `centralIsogenyRootDatumHom`,
  `splitCentralTorusQuotient`, `splitSimplyConnectedCorootSpan_of_inputs`,
  `splitCentralIsogenyExistence_of_commonTorusIsomorphism`,
  `splitRankOneCommonTorusIsomorphism_of_rootCell`,
  `splitCommonTorusIsomorphism_of_rankOne_of_leviGluing`,
  `LeviGluing.splitCommonTorusLeviGluing_of_algClosedGraphs`,
  `dynamicCentralizerReductive`, `dynamicCentralizerRoots` and the new
  declarations of this module.
- A name search over the closure for the strings `ParabolicDynamic`,
  `RegularCocharacterBorel`, `RankOneSolvable`, `RankOneBorelDynamic`,
  `RankOnePositiveRoot`, `ProjectiveBorel`, `BruhatCovering`,
  `SteinbergBigCell`, `GeometricReductivity` and `StructuralInputs` (either
  capitalization) found one constant, `maximalTorusCentralizer_of_structuralInputs`.
  It enters through `splitSemisimpleRootDatum`, via `maximalTorusCentralizer`.
  Its inputs are `dynamicCentralizerReductive`, `noTorusUnipotent` and
  `solvableTorusQuotient`, and the scan shows that its closure reaches no
  excluded name. The name only resembles the excluded
  `absoluteRootTangent_le_one_of_structuralInputs`.
- Controls: the same scan reports the excluded constants for the existing
  `splitSimplyConnectedCorootSpan` and `splitCentralIsogenyExistence`. It finds
  `rootDatumExistence`, `splitRankOneRootCell` and
  `rootLieLine_of_dynamicCentralizerReductive`, the last through
  `LeviGluing.algClosedGraphProjectionIsomorphisms`. These are exactly the three
  uses that this module replaces by hypotheses.

The module imports `SplitLeviGluingFactorInjectivity`, which imports
`RootLieLineFromTangent`, for the auxiliary lemmas it reuses (for example
`weightKernelTrivial_of_finrank_eq_one` and `weightKernelTrivial_reflection`).
The scan above shows that the excluded constants in these imported modules do
not enter the proofs.

## Provenance

The target is the necessity half of Milne's coroot criterion, Proposition 23.59
(J. S. Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
printed p.502, PDF p.518; printed page = PDF page − 16), proved there from the
Existence Theorem and the Isogeny Theorem (Corollary 23.56). The central Isogeny
Theorem is Milne Theorem 23.9. Its reduction to the Isomorphism Theorem for a
common torus (Theorem 23.25, Remark 23.26), through the central quotient, is the
Library's `splitCentralIsogenyExistence_of_commonTorusIsomorphism`. Milne's
proof of the Isomorphism Theorem uses the graph construction of Proposition
23.18 (printed p.491, PDF p.507). Its Lean form proves injectivity of the
differentials of the graph projections one weight space at a time. It needs
one-dimensional root spaces of the reductive graph group (Milne Theorem
21.11(b), printed p.428, PDF p.444: "dim g_α = 1"). This module takes that fact
as the explicit hypothesis `SplitRootLieLineStatement`. The rank-one case is
taken from the root cell of Conrad, *Reductive group schemes* (source ID
`conrad-2014-reductive-group-schemes`), Theorem 4.1.4 (PDF p.110) and Theorem
4.2.6 (PDF pp.120–121). Bundling the three inputs into
`SplitCorootSpanLineInputs` is an internal decomposition of this proof. Its
purpose is to keep the dependence on root-datum existence, the rank-one cell
and the root lines explicit, so that independent proofs of these statements can
be substituted.
