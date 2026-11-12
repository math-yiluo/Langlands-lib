# Proof of the full and sharp chamber Iwahori decompositions

Worker 4341. The theorem
`Langlands.Geometry.Building.ParahoricBuildingData.chamberIwahoriDecomposition`
proves exactly
`Langlands.Geometry.Building.ParahoricBuildingData.ChamberIwahoriDecompositionStatement`
from `Langlands.Geometry.Building.ChamberIwahoriStatement`. It holds for every
actual `P : ParahoricBuildingData G`, over every nonarchimedean local field `F`,
at arbitrary universe `u`. The variables and binders are those of the statement
module: `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, `G` a group scheme over `Spec F` with
`[IsAffineHom G.X.hom]`, and `P`. The theorem adds no premise. In particular it
does not assume an Iwahori decomposition, compact openness, building validity
or any conclusion of the target. The target's own premises are kept: the
corrected apartment axioms `P.apartment.SatisfiesApartmentAxioms P.centralizer`,
chamber membership, genericity of `ν`, and, for facets, the face relation and the
facet/chamber positive-system condition.

The conclusion is the complete published conjunction. It contains the sharp
chamber and facet conclusions (`ChamberSharpConclusion`,
`ChamberSharpFacetConclusion`) and the full ones (`ChamberIwahoriConclusion`,
`ChamberIwahoriFacetConclusion`). Their content is documented in
`ChamberIwahoriStatement.md` and `ChamberSharpStatement.md`. The full ones are:
`I_C = P_x`; the centralizer intersection with the actual `Z(F)^0`; equality of
the full and sharp unipotent intersections; injectivity and exact range of the
negative/central/positive product; and every fixed-sign ordered block bijection,
at both chamber depths. The facet clauses use negative depth `0+` and positive
depth `0`.

## Proof

The module proves three theorems in namespace
`Langlands.Geometry.Building.ParahoricBuildingData`.

1. `hasOppositeFactorPairs : RelativeRoot.HasOppositeFactorPairs P.i`. The
   published theorem `rootRankOneFactorization` (module
   `Langlands.GroupScheme.Rational.RootRankOneFactorizationProof`, KP 2.11.17)
   applies to the actual maximal split torus `P.i` of the connected reductive
   group `G`. It gives `RelativeRoot.HasRankOneFactorization P.i`. The torus
   `P.S` is split (`P.isMaximalSplitTorus.isSplitSubtorus.1`) and `G` is smooth
   (`P.isConnectedReductive.smooth`), so the published equivalence
   `RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs` turns this
   into opposite-pair existence.
2. `chamberIwahoriDecomposition_of_centralizerZeroIntersection`. It assumes
   `hZ : P.zeroDatum.CentralizerZeroIntersectionStatement`, that is
   `G(F)^0 ∩ Z(F)^1 = Z(F)^0` for the actual zero datum of `P`, and concludes
   `P.ChamberIwahoriDecompositionStatement`. The published
   `ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_intersection` (module
   `KPMinimalLeviZeroStatement`) derives the cover-image containment
   `P.zeroDatum.CoverImageCentralizerNormKernelStatement` from `hZ`. With the
   opposite pairs of item 1, this is exactly the input of the published
   `chamberIwahoriDecomposition_of_hasOppositeFactorPairs` (module
   `ChamberIwahoriFactorPairReduction`). This helper is an intermediate step
   only; the main theorem below discharges `hZ`.
3. `chamberIwahoriDecomposition : P.ChamberIwahoriDecompositionStatement`. It
   applies item 2 to the second conjunct of
   `ZeroSubgroupDatum.minimalLeviZeroComparison P.zeroDatum`. That is the
   published proof of KP Lemma 2.6.27 and Corollary 2.6.28 (module
   `KPMinimalLeviZeroComparisonProof`), which holds for every actual zero datum
   over a nonarchimedean local field.

Inside the published factor-pair reduction, the opposite pairs supply both
actual rank-one factorization and rational-point injectivity of the ordered root
products (`orderedRootPointInjectivity_of_hasOppositeFactorPairs`). Then
`chamberIwahoriDecomposition_of_localRootInjectivity` (module
`ChamberIwahoriPointReduction`) combines two published results:

- the sharp chamber and facet statement
  `chamberSharpDecomposition_of_localRootInjectivity` (KP Corollary 7.4.9 on
  `G(F)^♯`, with the factor bijections of Proposition 7.3.12(3),(5));
- the centralizer intersection
  `centralizerParahoricIntersection_of_rankOneFactorization` (module
  `PointParahoricCentralizer`, KP Lemma 7.4.3), which uses the cover-image
  containment.

It feeds them to `chamberIwahoriDecomposition_of_sharp` (module
`ChamberIwahoriReduction`), which derives the full-parahoric conclusions.

`lean_check` compiled the module with no diagnostics in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. The axioms of
`chamberIwahoriDecomposition` are `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

The original source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, together
with its corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`.

The sharp products are KP Corollary 7.4.9, printed p. 257 / PDF p. 288, with
the factor bijections of Proposition 7.3.12(3),(5). The full-parahoric steps are
derived as in KP §7.4. Definition 7.4.1(4) adjoins `Z(F)^0` to the sharp group.
Lemma 7.4.3 (printed p. 255 / PDF p. 286) gives `Z(F) ∩ P_Ω = Z(F)^0`, and
Lemma 7.4.4(1) (printed p. 256 / PDF p. 287) gives `I_C = P_x`. Uniqueness of factors comes from the open-cell
injectivity used in the proof of 7.3.12(5). The Lean derivation of these steps
is the published `chamberIwahoriDecomposition_of_sharp`; its route and
provenance are explained in `ChamberIwahoriReduction.md`.

The input `G(F)^0 ∩ Z(F)^1 = Z(F)^0` is KP Corollary 2.6.28. It is used here
only through its published Lean proof, and this module adds no new mathematical
claim beyond the composition described above.
