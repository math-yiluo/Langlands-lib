import Langlands.Geometry.Analytic.FullRecognitionControlledFinitePairs
import Langlands.Geometry.Analytic.FullRecognitionFiniteResidueBasePoints
import Langlands.Geometry.Analytic.FiniteSeparableCompletedResidue
import Langlands.Geometry.Analytic.FieldPointChartExtension
import Langlands.Geometry.Analytic.FieldPointValueChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueProof
import Langlands.Geometry.Analytic.EtaleSite
import Langlands.Geometry.Analytic.ValuedField.AlgebraicEmbedding
import Mathlib.FieldTheory.IsSepClosed

/-! # Points above a full base-field point lifted to a finite Galois extension -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set CategoryTheory
open AffinoidAtlasPresentation BanachSpectrum

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

/-- At the specified point over a full base-field point, a strong étale map
admits a full extension-valued source point with finite Galois values. -/
theorem IsEtaleAtAllPieces.exists_finiteGalois_fieldPoint
    {A B : AffinoidAtlasPresentation.{u, v, w} K}
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation} {z : A.space}
    (hg : g.IsEtaleAtAllPieces z) (p : FieldPoint K B.saturatedPresentation)
    (hp : p.point = g.baseMap z) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : NormedAlgebra K L)
      (_ : CompleteSpace L) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (q : FieldPoint L A.saturatedPresentation), q.point = z := by
  obtain ⟨i, hi⟩ := B.atlas.exists_mem_range_chart (g.baseMap z)
  obtain ⟨V, W, hVW, s, hs, hfinite, hetale, -, -, -⟩ :=
    hg.exists_pointed_fullRecognitionPair_within univ Filter.univ_mem i hi univ Filter.univ_mem
  let f := g.fullRecognitionPairs.pullback V W hVW
  let p' := p.map B.localDomainToFullRecognition B.atlas.saturatedAtlas_hasAllLocalDomains
  have hw : p'.point ∈ range W.chart := hp.symm ▸ hVW ⟨z, ⟨s, hs⟩, rfl⟩
  obtain ⟨t, ht, hnorm⟩ := p'.isChartPoint W hw
  have ht' : t = comap f.toBoundedRingHom s := by
    apply W.isEmbedding_chart.injective
    exact ht.trans ((g.fullRecognitionPairs.chart_comm V W hVW s).trans
      ((congrArg g.baseMap hs).trans hp.symm)).symm
  let c := p'.eval W hw
  have hc (a : W.algebra) : ‖c a‖ = (comap f.toBoundedRingHom s) a :=
    (hnorm a).trans (congrArg (fun t : BanachSpectrum W.algebra => t a) ht')
  have hfin : Module.Finite K (CompletedResidueField K s) :=
    finite_completedResidue_of_finite_over_baseFieldCharacter K f hfinite.finite s c hc
  let H := CompletedResidueField K s
  let : FiniteDimensional K H := hfin
  let : Algebra.IsSeparable K H :=
    @isSeparable_completedResidue_of_unramified_over_baseFieldCharacter K _ _ _ _ _ _ _ _ _ f
      hfinite.finite.finiteType s hetale.2 c hc hfin
  let S := SeparableClosure K
  let iHS : H →ₐ[K] S := IsSepClosed.lift
  let : Algebra H S := iHS.toRingHom.toAlgebra
  let : IsScalarTower K H S := IsScalarTower.of_algebraMap_eq fun a => (iHS.commutes a).symm
  let L := ↥(IntermediateField.normalClosure K H S)
  let : FiniteDimensional K L :=
    inferInstanceAs (FiniteDimensional K (IntermediateField.normalClosure K H S))
  let : IsGalois K L := IsGalois.normalClosure K H S
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  let : CompleteSpace L := spectralNorm.completeSpace K L
  let e : H →ₐ[K] L := (normalClosure.algHomEquiv K H S).symm iHS
  have he (a : H) : ‖e a‖ = ‖a‖ :=
    (isometry_algHom_of_isAlgebraic e).norm_map_of_map_zero (map_zero e) a
  let d := e.comp (completedResidueMap K s).toAlgHom
  have hd (a : V.algebra) : ‖d a‖ = s a :=
    (he _).trans (norm_completedResidueMap K s a)
  obtain ⟨q', ⟨hq', -, -⟩, -⟩ :=
    FieldPoint.existsUnique_of_chartCharacter (A := A.fullRecognitionPresentation)
      PresentedAffinoidAlgebra.domainCompletedResidueSurjectivity z V d ⟨s, hs, hd⟩
  let q := FieldPoint.comapQuasiIso A.localDomainToFullRecognition_isQuasiIso
    A.fullRecognitionPresentation_hasAllLocalDomains q'
  have hq := FieldPoint.map_comapQuasiIso A.localDomainToFullRecognition_isQuasiIso
    A.fullRecognitionPresentation_hasAllLocalDomains A.atlas.saturatedAtlas_hasAllLocalDomains q'
  have hpoint : q.point = q'.point := congrArg FieldPoint.point hq
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, hpoint.trans hq'⟩

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

/-- A localized étale arrow admits a full point with finite Galois values
at any specified point above the projection of a full base-field point. -/
theorem exists_finiteGalois_fieldPoint_of_etale
    {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y} (hf : etale f)
    (p : (localizedFieldPointFunctor K).obj Y) (z : localizedSpaceFunctor.obj X)
    (hz : localizedSpaceFunctor.map f z = ((localizedFieldPointProjection K).app Y p).down) :
    ∃ (L : Type u) (_ : NormedField L) (_ : IsUltrametricDist L) (_ : NormedAlgebra K L)
      (_ : CompleteSpace L) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (q : (localizedFieldPointFunctor L).obj X),
        ((localizedFieldPointProjection L).app X q).down = z := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let z' : A.space := localizedSpaceFunctor.map e.inv.left z
  let p' : FieldPoint K B.saturatedPresentation := (localizedFieldPointFunctor K).map e.inv.right p
  have hi : e.inv.left ≫ localizationFunctor.map g = f ≫ e.inv.right := e.inv.w
  have hc : localizedSpaceFunctor.map (localizationFunctor.map g) z' = p'.point := by
    change localizedSpaceFunctor.map (localizationFunctor.map g)
      (localizedSpaceFunctor.map e.inv.left z) = _
    rw [← TopCat.comp_app, ← Functor.map_comp, hi, Functor.map_comp, TopCat.comp_app, hz]
    exact (localizedFieldPointProjection_down_naturality e.inv.right p).symm
  have hp' : p'.point = g.baseMap z' := by
    rw [localizedSpaceFunctor_map] at hc
    exact hc.symm
  obtain ⟨L, _, _, _, _, _, _, q, hq⟩ := (hg z').exists_finiteGalois_fieldPoint p' hp'
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, (localizedFieldPointFunctor L).map e.hom.left q, ?_⟩
  have hproj := localizedFieldPointProjection_down_naturality e.hom.left q
  change _ = localizedSpaceFunctor.map e.hom.left q.point at hproj
  refine hproj.trans ?_
  rw [hq]
  change localizedSpaceFunctor.map e.hom.left (localizedSpaceFunctor.map e.inv.left z) = z
  have hleft : e.inv.left ≫ e.hom.left = 𝟙 X := Arrow.inv_hom_id_left e
  rw [← TopCat.comp_app, ← Functor.map_comp, hleft]
  exact congrArg (fun m : localizedSpaceFunctor.obj X ⟶ localizedSpaceFunctor.obj X => m z)
    (localizedSpaceFunctor.map_id X)

end SaturatedAtlasPresentation

end Langlands.Analytic
