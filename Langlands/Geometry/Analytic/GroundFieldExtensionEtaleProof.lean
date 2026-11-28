import Langlands.Geometry.Analytic.GroundFieldExtensionEtaleStatement
import Langlands.Geometry.Analytic.GroundFieldExtensionQuasiEtaleReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionFiniteTensor
import Langlands.Geometry.Analytic.AdmissibleRecognitionSubatlas
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityProof
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof
import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonProof

/-! # Scalar extension preserves étale and quasi-étale morphisms -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Set Filter Topology PresentedAffinoidAlgebra
open scoped Topology

section FullRecognition

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
private theorem finiteEtale_of_heq
    {A B A' B' : PresentedAffinoidAlgebra K} {f : BoundedAlgHom K A B}
    {f' : BoundedAlgHom K A' B'} (ha : A' = A) (hb : B' = B) (h : HEq f' f)
    (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale) :
    f'.IsFiniteBanach ∧ f'.AlgebraicallyFiniteEtale := by
  cases ha
  cases hb
  cases eq_of_heq h
  exact ⟨hf, he⟩

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} (f : CompatibleStrongHom A B)

private abbrev originalRecognized (A : AffinoidAtlasPresentation.{u, v, w} K) (i : A.atlas.Index) :=
  A.atlas.saturatedAtlas.originalRecognitionIndex (A.atlas.originalSaturatedIndex i)

/-- Both the saturated chart comparison and full recognition retain the
finite étale property of an admissible original pair. -/
private theorem originalRecognized_finiteEtale (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hb : (f.pullback i j h).IsFiniteBanach) (he : (f.pullback i j h).AlgebraicallyFiniteEtale) :
    ∃ h' : f.saturationExtension.baseMap '' range (originalRecognized A i).chart ⊆
      range (originalRecognized B j).chart,
      (f.saturationExtension.fullRecognitionPairs.pullback (originalRecognized A i)
        (originalRecognized B j) h').IsFiniteBanach ∧
      (f.saturationExtension.fullRecognitionPairs.pullback (originalRecognized A i)
        (originalRecognized B j) h').AlgebraicallyFiniteEtale := by
  let s : A.atlas.saturatedAtlas.Index := A.atlas.originalSaturatedIndex i
  let t : B.atlas.saturatedAtlas.Index := B.atlas.originalSaturatedIndex j
  let x := originalRecognized A i
  let y := originalRecognized B j
  let g := f.saturationExtension
  let h₀ := f.toStrongHom.saturationExtension_original_admissible i j h
  have h₁ : g.baseMap '' range x.chart ⊆ range y.chart :=
    ((Set.image_mono (A.atlas.saturatedAtlas.recognitionAtlas_original_range s).subset).trans
      h₀).trans (B.atlas.saturatedAtlas.recognitionAtlas_original_range t).superset
  refine ⟨h₁, ?_⟩
  have ⟨hb₀, he₀⟩ := finiteEtale_of_heq
    (A := B.atlas.algebra j) (B := A.atlas.algebra i)
    (B.atlas.saturatedAtlas_original_algebra j) (A.atlas.saturatedAtlas_original_algebra i)
    (f.toStrongHom.saturationExtension_pullback_original f.coherent i j h) hb he
  let eA := A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv s
  let eB := B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv t
  have hcomm : eA.toBoundedAlgHom.comp (g.fullRecognitionPairs.pullback x y h₁) =
      (g.pullback s t h₀).comp eB.toBoundedAlgHom :=
    (congrArg (·.comp (g.fullRecognitionPairs.pullback x y h₁))
      (A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv_toBoundedAlgHom s)).trans
        ((g.originalRestriction_comp_fullRecognitionPairs x y h₁ s
          (A.atlas.saturatedAtlas.originalRecognitionIndex_range_subset s) t
          (B.atlas.saturatedAtlas.originalRecognitionIndex_range_subset t) h₀).trans
            (congrArg ((g.pullback s t h₀).comp ·)
              (B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv_toBoundedAlgHom t).symm))
  have hmap : g.fullRecognitionPairs.pullback x y h₁ =
      eA.symm.toBoundedAlgHom.comp ((g.pullback s t h₀).comp eB.toBoundedAlgHom) := by
    apply BoundedAlgHom.ext
    intro a
    apply eA.injective
    have h := congrArg (fun φ : BoundedAlgHom K y.algebra (A.atlas.saturatedAtlas.algebra s) => φ a) hcomm
    change eA (g.fullRecognitionPairs.pullback x y h₁ a) =
      eA (eA.symm (g.pullback s t h₀ (eB a)))
    exact h.trans (eA.apply_symm_apply _).symm
  rw [hmap]
  exact ⟨eA.symm.isFiniteBanach.comp (hb₀.comp eB.isFiniteBanach),
    (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ eA.symm.toAlgEquiv.bijective).comp
      (he₀.comp (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ eB.toAlgEquiv.bijective))⟩

end FullRecognition

section ScalarExtension

open SaturatedAtlasPresentation
open PresentedAffinoidAlgebra.GroundFieldExtension (map map_isFiniteBanach map_algebraicallyFiniteEtale)
open IndexedAffinoidAtlas.GroundFieldExtension (projection continuous_projection range_chart)

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : AffinoidAtlasPresentation.{u, v, v} K} (g : ofSaturation A ⟶ ofSaturation B)

private abbrev extendedPresentation (P : AffinoidAtlasPresentation.{u, v, v} K) :=
  IndexedAffinoidAtlas.GroundFieldExtension.presentation K L P.atlas

private abbrev extendedRecognized (P : AffinoidAtlasPresentation.{u, v, v} K)
    (i : P.atlas.Index) := originalRecognized (extendedPresentation K L P) i

private theorem extendedRecognized_locus (P : AffinoidAtlasPresentation.{u, v, v} K)
    (i : P.atlas.Index) :
    (extendedRecognized K L P i).locus = projection K L P.atlas ⁻¹' range (P.atlas.chart i) := by
  let a := (extendedPresentation K L P).atlas
  let j := a.originalSaturatedIndex i
  let T := extendedRecognized K L P i
  exact T.range_chart.symm.trans ((a.saturatedAtlas.recognitionAtlas_original_range j).trans
    ((a.saturatedAtlas_original_range i).trans (range_chart K L P.atlas i)))

private abbrev recognizedSource : SaturatedAtlasPresentation.{u, v, v} K :=
  ⟨g.recognitionSource, g.recognitionSource_hasAllLocalDomains⟩

private abbrev recognizedTarget : SaturatedAtlasPresentation.{u, v, v} K :=
  ofFullRecognition B

private abbrev recognizedHom : recognizedSource K g ⟶ recognizedTarget K (B := B) :=
  g.recognitionMap

private abbrev sourceL : AffinoidAtlasPresentation.{u', max u' v, v} L :=
  extendedPresentation K L g.recognitionSource

private abbrev targetL : AffinoidAtlasPresentation.{u', max u' v, v} L :=
  extendedPresentation K L B.fullRecognitionPresentation

private abbrev extendedHom : ofSaturation (sourceL K L g) ⟶ ofSaturation (targetL K L (B := B)) :=
  (compatibleMap K L g.compatibleRecognitionMap).saturationExtension

private abbrev pA := projection K L g.recognitionSource.atlas
private abbrev pB := projection K L B.fullRecognitionPresentation.atlas

private theorem extendedHom_naturality (x : (sourceL K L g).space) :
    pB K L (B := B) ((extendedHom K L g).baseMap x) = g.baseMap (pA K L g x) :=
  projection_pointMap K L g.recognitionMap g.compatibleRecognitionMap.compatible x

private theorem extendedRecognizedFiniteEtale (V : Set A.space) (U : Set B.space)
    (hfin : StrongHom.IsFiniteEtaleOver (A := A) (B := B) g V U)
    (W : B.atlas.saturatedAtlas.RecognizedSubset) (hW : W.locus ⊆ U) :
    let W' := extendedRecognized K L B.fullRecognitionPresentation W
    ∃ (P' : (sourceL K L g).atlas.saturatedAtlas.RecognizedSubset)
      (h' : (extendedHom K L g).baseMap '' range P'.chart ⊆ range W'.chart),
      P'.locus = pA K L g ⁻¹' V ∩ (extendedHom K L g).baseMap ⁻¹' W'.locus ∧
      ((extendedHom K L g).fullRecognitionPairs.pullback P' W' h').IsFiniteBanach ∧
      ((extendedHom K L g).fullRecognitionPairs.pullback P' W' h').AlgebraicallyFiniteEtale := by
  dsimp only
  obtain ⟨P, h, hPl, hb, he⟩ := hfin.2 W hW
  let i := g.recognitionSourceIndex P W h
  let f := g.compatibleRecognitionMap
  let fL := compatibleMap K L f
  have hL := (admissible_iff K L f.toStrongHom f.compatible i W).2 h
  have hbL : (fL.pullback i W hL).IsFiniteBanach :=
    map_isFiniteBanach L (g.fullRecognitionPairs.pullback P W h) hb
  have heL : (fL.pullback i W hL).AlgebraicallyFiniteEtale :=
    map_algebraicallyFiniteEtale L (g.fullRecognitionPairs.pullback P W h) hb he
  obtain ⟨h', hb', he'⟩ := originalRecognized_finiteEtale fL i W hL hbL heL
  let P' := extendedRecognized K L g.recognitionSource i
  let W' := extendedRecognized K L B.fullRecognitionPresentation W
  refine ⟨P', h', ?_, hb', he'⟩
  have hP' : P'.locus = pA K L g ⁻¹' P.locus :=
    (extendedRecognized_locus K L g.recognitionSource i).trans (congrArg (Set.preimage (pA K L g)) P.range_chart)
  have hW' : W'.locus = pB K L (B := B) ⁻¹' W.locus :=
    (extendedRecognized_locus K L B.fullRecognitionPresentation W).trans
      (congrArg (Set.preimage (pB K L (B := B))) W.range_chart)
  change P'.locus = _ ∩ (extendedHom K L g).baseMap ⁻¹' W'.locus
  rw [hP', hW', hPl]
  ext x
  change (pA K L g x ∈ V ∧ g.baseMap (pA K L g x) ∈ W.locus) ↔
    (pA K L g x ∈ V ∧ pB K L (B := B) ((extendedHom K L g).baseMap x) ∈ W.locus)
  exact Iff.of_eq (congrArg (fun y => pA K L g x ∈ V ∧ y ∈ W.locus)
    (extendedHom_naturality K L g x).symm)

private abbrev extendedTargetIndex (W : B.atlas.saturatedAtlas.RecognizedSubset) :=
  extendedRecognized K L B.fullRecognitionPresentation W

private theorem extendedTargetIndex_locus (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (extendedTargetIndex K L W).locus = pB K L (B := B) ⁻¹' W.locus :=
  (extendedRecognized_locus K L B.fullRecognitionPresentation W).trans
    (congrArg (Set.preimage (pB K L (B := B))) W.range_chart)

private theorem finiteEtaleTargetFamilies (V : Set A.space) (U : Set B.space)
    (hU : IsOpen U) (hfin : StrongHom.IsFiniteEtaleOver (A := A) (B := B) g V U)
    (z : (targetL K L (B := B)).space) (hz : pB K L (B := B) z ∈ U) :
    ∃ I : Set (targetL K L (B := B)).atlas.saturatedAtlas.RecognizedSubset, I.Finite ∧
      (∀ W ∈ I, z ∈ W.locus ∧ W.locus ⊆ pB K L (B := B) ⁻¹' U ∧
        ∃ (P : (sourceL K L g).atlas.saturatedAtlas.RecognizedSubset)
          (h : (extendedHom K L g).baseMap '' range P.chart ⊆ range W.chart),
          P.locus = pA K L g ⁻¹' V ∩ (extendedHom K L g).baseMap ⁻¹' W.locus ∧
          ((extendedHom K L g).fullRecognitionPairs.pullback P W h).IsFiniteBanach ∧
          ((extendedHom K L g).fullRecognitionPairs.pullback P W h).AlgebraicallyFiniteEtale) ∧
      (⋃ W ∈ I, W.locus) ∈ 𝓝 z := by
  obtain ⟨I, hI, hIU, hIn⟩ := B.atlas.exists_finite_recognized_nhds_subset
    (pB K L (B := B) z) U (hU.mem_nhds hz)
  let j := extendedTargetIndex K L (B := B)
  refine ⟨j '' I, hI.image _, ?_, ?_⟩
  · rintro _ ⟨W, hW, rfl⟩
    obtain ⟨hzW, hWU⟩ := hIU W hW
    have hEq : (j W).locus = pB K L (B := B) ⁻¹' W.locus := extendedTargetIndex_locus K L W
    exact ⟨hEq.symm.subset hzW, hEq.subset.trans (preimage_mono hWU),
      extendedRecognizedFiniteEtale K L g V U hfin W hWU⟩
  · have hcont : Continuous (pB K L (B := B)) := continuous_projection K L B.fullRecognitionPresentation.atlas
    refine mem_of_superset (hcont.continuousAt.preimage_mem_nhds hIn) ?_
    intro x hx
    obtain ⟨W, hW, hxW⟩ := mem_iUnion₂.mp (show pB K L (B := B) x ∈ ⋃ W ∈ I, W.locus from hx)
    exact mem_iUnion₂.mpr ⟨j W, ⟨W, hW, rfl⟩, (extendedTargetIndex_locus K L W).superset hxW⟩

set_option maxHeartbeats 700000 in
/-- The extended local finite étale models give the finite-piece criterion
at each point, then give étaleness over all recognized affinoid pieces. -/
private theorem extendedHom_isEtaleAllPieces
    (hg : StrongHom.IsEtaleAllPieces (A := A) (B := B) g) :
    (extendedHom K L g).IsEtaleAllPieces := by
  let AL := sourceL K L g
  let BL := targetL K L (B := B)
  let G := extendedHom K L g
  have hpoint (y : AL.space) : G.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y := by
    obtain ⟨V, U, hV, hU, hy, hfin⟩ :=
      StrongHom.strongEtaleLocallyFiniteEtale (K := K) A B g hg (pA K L g y)
    let V' := pA K L g ⁻¹' V
    let U' := pB K L (B := B) ⁻¹' U
    have hV' : IsOpen V' := hV.preimage (continuous_projection K L g.recognitionSource.atlas)
    have hU' : IsOpen U' := hU.preimage (continuous_projection K L B.fullRecognitionPresentation.atlas)
    have hVU : G.baseMap '' V' ⊆ U' := by
      rintro _ ⟨x, hx, rfl⟩
      exact (congrArg (· ∈ U) (extendedHom_naturality K L g x)).mpr (hfin.1 ⟨_, hx, rfl⟩)
    have hfamily : G.HasFiniteTargetFamilies V' U' := by
      intro x hx
      obtain ⟨I, hI, hIprop, hIn⟩ := finiteEtaleTargetFamilies K L g V U hU hfin x hx
      refine ⟨I, hI, fun W hW => ?_, hIn⟩
      obtain ⟨hxW, hWU, P, hPW, hp, hb, _⟩ := hIprop W hW
      exact ⟨hxW, hWU, P, hPW, hp, hb⟩
    have hfinite : G.IsFiniteOver V' U' :=
      StrongHom.finiteOverTargetLocality L AL BL G V' U' hV' hU' hVU hfamily
    obtain ⟨I, hI, hIprop, hIn⟩ := finiteEtaleTargetFamilies K L g V U hU hfin
      (G.baseMap y) (hVU ⟨y, hy, rfl⟩)
    apply StrongHom.finitePiecesEtaleAllPieces AL BL G y
    refine ⟨V', U', hV', hU', hy, hfinite, I, hI,
      fun W hW => ⟨(hIprop W hW).2.1, (hIprop W hW).1⟩, hIn, ?_⟩
    intro W hW P hPW hP s _
    obtain ⟨_, _, Q, hQW, hQ, _, hqe⟩ := hIprop W hW
    have hPQ : P = Q := Subtype.ext (Subtype.ext (hP.trans hQ.symm))
    subst Q
    exact hqe.isEtaleAtPoint s
  intro y
  exact ⟨univ, isOpen_univ, mem_univ y,
    fun z _ => StrongHom.hasAllPiecesAt_isEtaleAtPoint_iff.mp (hpoint z)⟩

private def recognitionArrowIso :
    Arrow.mk (localizationFunctor.map g) ≅ Arrow.mk (localizationFunctor.map (recognizedHom K g)) := by
  let a : ofSaturation A ⟶ recognizedSource K g := g.recognitionSourceComparison
  let b : ofSaturation B ⟶ recognizedTarget K (B := B) := B.localDomainToFullRecognition
  let ea := localizedQuasiIso a g.recognitionSourceComparison_isQuasiIso
  let eb := localizedQuasiIso b B.localDomainToFullRecognition_isQuasiIso
  refine Arrow.isoMk ea eb ?_
  change localizationFunctor.map a ≫ localizationFunctor.map (recognizedHom K g) =
    localizationFunctor.map g ≫ localizationFunctor.map b
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg localizationFunctor.map g.recognitionSourceComparison_comp

/-- Scalar extension of an étale strong representative is étale in the
localized analytic category. -/
private theorem etale_extendedStrong
    (hg : StrongHom.IsEtaleAllPieces (A := A) (B := B) g) :
    etale ((localizedFunctor K L).map (localizationFunctor.map g)) := by
  let F := localizedFunctor K L
  let G := extendedHom K L g
  have hG := extendedHom_isEtaleAllPieces K L g hg
  have he : etale (localizationFunctor.map G) :=
    etale_map_of_strongEtale G ((strongEtale_ofSaturation_iff_isEtaleAllPieces G).mpr hG)
  have hmap : F.map (localizationFunctor.map (recognizedHom K g)) = localizationFunctor.map G :=
    localizedFunctor_map K L _
  have he' : etale (F.map (localizationFunctor.map (recognizedHom K g))) :=
    (congrArg (fun f => etale (K := L) f) hmap).mpr he
  exact (etale.arrow_mk_iso_iff (F.mapArrow.mapIso (recognitionArrowIso K g))).mpr he'

/-- The actual localized scalar-extension functor preserves étale arrows. -/
theorem etale_localizedFunctor_map
    {Y X : LocalizedCategory.{u, v, v} (K := K)} {f : Y ⟶ X} (hf : etale f) :
    etale ((localizedFunctor K L).map f) := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  exact (etale.arrow_mk_iso_iff ((localizedFunctor K L).mapArrow.mapIso e)).mp
    (etale_extendedStrong K L g hg)

end ScalarExtension

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

namespace Langlands.Analytic.SaturatedAtlasPresentation

open AffinoidAtlasPresentation.GroundFieldExtension

/-- Étale maps and the local factorizations of quasi-étale maps are preserved
by the actual ground-field extension functor. -/
theorem groundFieldExtensionEtale : GroundFieldExtensionEtaleStatement.{u, u', v} := by
  intro K _ _ _ L _ _ _ _ Y X f
  exact ⟨etale_localizedFunctor_map K L, quasiEtale_scalarExtension_of_preservesEtale K L
    (fun _ hf => etale_localizedFunctor_map K L hf) f⟩

end Langlands.Analytic.SaturatedAtlasPresentation
