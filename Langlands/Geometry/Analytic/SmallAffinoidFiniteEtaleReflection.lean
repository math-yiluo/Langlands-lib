import Langlands.Geometry.Analytic.FiniteCompactNeighborhoods
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.FullRecognitionIsomorphismCriterion
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.SmallAffinoidEtaleRealization

/-! # Reflection of finite étaleness on a small affinoid spectrum -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open Set PresentedAffinoidAlgebra AffinoidAtlasPresentation SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R S : PresentedAffinoidAlgebra K}
  [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]

omit [CompleteSpace K] [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] in
private theorem finiteEtale_transport
    {R' S' : PresentedAffinoidAlgebra K} (hR : R' = R) (hS : S' = S)
    {f' : BoundedAlgHom K R' S'} {f : BoundedAlgHom K R S}
    (h : HEq f' f) :
    (f'.IsFiniteBanach ↔ f.IsFiniteBanach) ∧
      (f'.AlgebraicallyFiniteEtale ↔ f.AlgebraicallyFiniteEtale) := by
  cases hR
  cases hS
  cases eq_of_heq h
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- On small affinoid spectra, analytic étaleness reflects algebraic finite
étaleness for a finite Banach map. -/
theorem algebraicallyFiniteEtale_of_map_etale (f : BoundedAlgHom K R S)
    (hf : f.IsFiniteBanach) (he : etale (localizationFunctor.map (map f))) :
    f.AlgebraicallyFiniteEtale := by
  let A := (saturated.{u, v} S).presentation
  let B := (saturated.{u, v} R).presentation
  let F : StrongHom A.saturatedPresentation B.saturatedPresentation := canonicalMap f
  let i : A.atlas.saturatedAtlas.Index := canonicalGlobalChart S
  let j : B.atlas.saturatedAtlas.Index := canonicalGlobalChart R
  have hi : range (A.atlas.saturatedAtlas.chart i) = univ := canonicalGlobalChart_range S
  have hj : range (B.atlas.saturatedAtlas.chart j) = univ := canonicalGlobalChart_range R
  have h : F.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j) := canonicalGlobalChart_admissible f
  have hTransport := finiteEtale_transport
    (canonicalGlobalChart_algebra R) (canonicalGlobalChart_algebra S)
    (canonicalMap_pullback_global_heq f)
  have hFinite := F.isFiniteOver_of_charts i j h (hTransport.1.mpr hf)
  rw [hi, hj] at hFinite
  have heStrong : F.IsEtaleAllPieces :=
    (etale_localizationFunctor_map_iff_strongEtale (map f)).mp he
  have hFiniteEtale := heStrong.isFiniteEtaleOver isOpen_univ hFinite
  let P := A.atlas.saturatedAtlas.originalRecognitionIndex i
  let W := B.atlas.saturatedAtlas.originalRecognitionIndex j
  have hP : P.locus = univ := hi
  have hW : W.locus = univ := hj
  obtain ⟨P', hPW, hP', -, hEt⟩ := hFiniteEtale.2 W (subset_univ _)
  have hPP : P' = P := by
    apply Subtype.ext
    apply Subtype.ext
    change P'.locus = P.locus
    rw [hP', hW, hP]
    exact Set.eq_univ_of_forall fun _ => ⟨mem_univ _, mem_univ _⟩
  subst hPP
  let eP := A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv i
  let eW := B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv j
  let g : BoundedAlgHom K W.algebra P.algebra := F.fullRecognitionPairs.pullback P W hPW
  have hCom : eP.toBoundedAlgHom.comp g =
      (F.pullback i j h).comp eW.toBoundedAlgHom := by
    change (A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv i).toBoundedAlgHom.comp g =
      (F.pullback i j h).comp
        (B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv j).toBoundedAlgHom
    rw [A.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv_toBoundedAlgHom,
      B.atlas.saturatedAtlas.originalRecognitionRestrictionEquiv_toBoundedAlgHom]
    exact F.originalRestriction_comp_fullRecognitionPairs P W hPW i
      (A.atlas.saturatedAtlas.originalRecognitionIndex_range_subset i)
      j (B.atlas.saturatedAtlas.originalRecognitionIndex_range_subset j) h
  have hEq : F.pullback i j h = (eP.toBoundedAlgHom.comp g).comp eW.symm.toBoundedAlgHom := by
    ext x
    have hx := congrArg (fun m : BoundedAlgHom K W.algebra
      (A.atlas.saturatedAtlas.algebra i) => m (eW.symm x)) hCom
    change F.pullback i j h x = eP (g (eW.symm x))
    exact (congrArg (F.pullback i j h) (eW.apply_symm_apply x)).symm.trans hx.symm
  apply hTransport.2.mp
  change (F.pullback i j h).AlgebraicallyFiniteEtale
  rw [hEq]
  exact ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _
    eP.toAlgEquiv.bijective).comp hEt).comp
      (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ eW.toAlgEquiv.symm.bijective)

end Langlands.Analytic.SmallAffinoidSpectrum
