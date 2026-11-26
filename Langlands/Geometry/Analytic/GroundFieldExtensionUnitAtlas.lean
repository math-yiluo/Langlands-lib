import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionUnit
import Langlands.Geometry.Analytic.GroundFieldExtensionFunctor
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # The identity ground-field extension of an analytic atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open _root_.CategoryTheory Set Topology
open AffinoidAtlasPresentation PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Space

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "C" => chartSystem K K a

private theorem projection_bijective : Function.Bijective (projection K K a) := by
  refine ⟨?_, projection_surjective K K a⟩
  intro x y h
  obtain ⟨i, s, rfl⟩ := (C).exists_chart x
  have hy : y ∈ range ((C).chart i) := by
    rw [range_chart, mem_preimage, ← h, projection_chart]
    exact mem_range_self _
  obtain ⟨t, rfl⟩ := hy
  apply congrArg ((C).chart i)
  apply (unitSpectrumHomeomorph K (a.algebra i)).injective
  apply (a.isEmbedding_chart i).injective
  exact h

private def unitPointEquiv : (C).Space ≃ X :=
  Equiv.ofBijective (projection K K a) (projection_bijective K a)

private theorem unitPointEquiv_symm_chart (i : a.Index) (x : BanachSpectrum (a.algebra i)) :
    (unitPointEquiv K a).symm (a.chart i x) =
      (C).chart i ((unitSpectrumHomeomorph K (a.algebra i)).symm x) := by
  apply (unitPointEquiv K a).injective
  rw [Equiv.apply_symm_apply]
  change a.chart i x = projection K K a ((C).chart i ((unitSpectrumHomeomorph K (a.algebra i)).symm x))
  rw [projection_chart, ← unitSpectrumHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The actual scalar-extension projection along the identity is a homeomorphism. -/
def unitHomeomorph : (C).Space ≃ₜ X where
  toEquiv := unitPointEquiv K a
  continuous_toFun := continuous_projection K K a
  continuous_invFun := by
    apply a.isNet_chartFamily.1.continuous
    rintro _ ⟨i, rfl⟩
    apply continuousOn_iff_continuous_domRestrict.mpr
    let e := (a.isEmbedding_chart i).toHomeomorph
    refine (((C).continuous_chart i).comp
      ((unitSpectrumHomeomorph K (a.algebra i)).symm.continuous.comp e.symm.continuous)).congr ?_
    intro x
    have he : a.chart i (e.symm x) = x.val :=
      congrArg Subtype.val (e.apply_symm_apply x)
    change (C).chart i ((unitSpectrumHomeomorph K (a.algebra i)).symm (e.symm x)) =
      (unitPointEquiv K a).symm x.val
    exact (unitPointEquiv_symm_chart K a i (e.symm x)).symm.trans
      (congrArg (unitPointEquiv K a).symm he)

@[simp] theorem unitHomeomorph_apply (x : (C).Space) :
    unitHomeomorph K a x = projection K K a x := rfl

end Space

section Strong

variable (A : AffinoidAtlasPresentation.{u, max u w, w} K)

local notation "a" => A.atlas
local notation "C" => presentation K K a
local notation "π" => projection K K a

private theorem unit_range_of_admissible (i j : (a).Index)
    (h : π '' range ((C).atlas.chart i) ⊆ range ((a).chart j)) :
    range ((a).chart i) ⊆ range ((a).chart j) :=
  (projection_image_chart K K a i).superset.trans h

private def unitStrongMap : StrongHom C A where
  baseMap := ⟨π, continuous_projection K K a⟩
  target_exists i := ⟨i, (projection_image_chart K K a i).subset⟩
  pullback i j h := (unitEquiv K ((a).algebra i)).toBoundedAlgHom.comp
    ((a).restriction i j (unit_range_of_admissible K A i j h))
  chart_comm i j h x :=
    ((a).restriction_chart i j (unit_range_of_admissible K A i j h)
      (unitSpectrumHomeomorph K ((a).algebra i) x)).trans (projection_chart K K a i x).symm
  restriction_comm i i' j j' hi hj h h' := by
    let hi₀ := (range_chart_subset_iff K K a i i').mp hi
    let hj₀ := unit_range_of_admissible K A i j h
    let hj₁ := unit_range_of_admissible K A i' j' h'
    ext x
    change map K K ((a).restriction i i' hi₀)
        (iota K K ((a).algebra i') ((a).restriction i' j' hj₁ x)) =
      iota K K ((a).algebra i) ((a).restriction i j hj₀ ((a).restriction j j' hj x))
    rw [map_iota]
    exact congrArg (fun φ : BoundedAlgHom K ((a).algebra j') ((a).algebra i) =>
      iota K K ((a).algebra i) (φ x))
      (((a).restriction_comp i i' j' hi₀ hj₁ (hi₀.trans hj₁)).symm.trans
        ((a).restriction_comp i j j' hj₀ hj (hi₀.trans hj₁)))

/-- Projection along the identity as a compatible strong map with all of
its bounded chart pullbacks. -/
def unitCompatibleMap : CompatibleStrongHom C A where
  toStrongHom := unitStrongMap K A
  compatible := (unitStrongMap K A).hasLocallyCompatiblePullbacks_iff.2 (by
    intro i j k hj hk
    have hj₀ : (StrongHom.id A).baseMap '' range ((a).chart i) ⊆ range ((a).chart j) := by
      simpa only [StrongHom.id, ContinuousMap.coe_id, image_id] using
        unit_range_of_admissible K A i j hj
    have hk₀ : (StrongHom.id A).baseMap '' range ((a).chart i) ⊆ range ((a).chart k) := by
      simpa only [StrongHom.id, ContinuousMap.coe_id, image_id] using
        unit_range_of_admissible K A i k hk
    exact (StrongHom.hasCoherentPullbacks_id A i j k hj₀ hk₀).comp a
      (unitEquiv K ((a).algebra i)).toBoundedAlgHom)

theorem unitCompatibleMap_isQuasiIso : (unitCompatibleMap K A).toStrongHom.IsQuasiIso := by
  refine ⟨(unitHomeomorph K a).isHomeomorph, ?_⟩
  intro i j h
  change A.atlas.Index at i
  let h₀ := unit_range_of_admissible K A i j h
  change Represents K ((unitEquiv K ((a).algebra i)).toBoundedAlgHom.comp ((a).restriction i j h₀))
    ((a).chart j ⁻¹' (π '' range ((chartSystem K K a).chart i)))
  rw [projection_image_chart]
  exact ((a).restriction_represents i j h₀).postcomp_equiv (unitEquiv K ((a).algebra i))

theorem unitCompatibleMap_pullback_same (i : (a).Index)
    (hi : (unitCompatibleMap K A).baseMap '' range ((C).atlas.chart i) ⊆ range ((a).chart i)) :
    (unitCompatibleMap K A).pullback i i hi = (unitEquiv K ((a).algebra i)).toBoundedAlgHom := by
  change (unitEquiv K ((a).algebra i)).toBoundedAlgHom.comp ((a).restriction i i _) = _
  rw [(a).restriction_id, BoundedAlgHom.comp_id]

end Strong

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory Set Topology
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, max u w, w} K}

/-- The compatible projection along the identity is natural for all original
compatible analytic morphisms. -/
theorem unitCompatibleMap_naturality (f : CompatibleStrongHom A B) :
    (compatibleMap K K f).comp (unitCompatibleMap K B) =
      (unitCompatibleMap K A).comp f := by
  let F := compatibleMap K K f
  let a := unitCompatibleMap K A
  let b := unitCompatibleMap K B
  have hb : (F.comp b).baseMap = (a.comp f).baseMap := by
    ext z
    exact projection_pointMap K K f.toStrongHom f.compatible z
  refine CompatibleStrongHom.ext_of_pullback hb ?_
  intro (i : A.atlas.Index)
  obtain ⟨j, hj⟩ := f.target_exists i
  have hF : F.baseMap '' range ((presentation K K A.atlas).atlas.chart i) ⊆
      range ((presentation K K B.atlas).atlas.chart j) :=
    (admissible_iff K K f.toStrongHom f.compatible i j).2 hj
  have ha : a.baseMap '' range ((presentation K K A.atlas).atlas.chart i) ⊆
      range (A.atlas.chart i) :=
    (projection_image_chart K K A.atlas i).subset
  have hb' : b.baseMap '' range ((presentation K K B.atlas).atlas.chart j) ⊆
      range (B.atlas.chart j) :=
    (projection_image_chart K K B.atlas j).subset
  have h := F.toStrongHom.comp_admissible b.toStrongHom i j j hF hb'
  refine ⟨j, h, ?_⟩
  let h' := a.toStrongHom.comp_admissible f.toStrongHom i i j ha hj
  change (F.comp b).pullback i j h = (a.comp f).pullback i j h'
  rw [CompatibleStrongHom.comp_pullback F b i j j hF hb' h,
    CompatibleStrongHom.comp_pullback a f i i j ha hj h']
  have hA := unitCompatibleMap_pullback_same K A i ha
  have hB := unitCompatibleMap_pullback_same K B j hb'
  change (F.pullback i j hF).comp (b.pullback j j hb') =
    (a.pullback i i ha).comp (f.pullback i j hj)
  rw [show b.pullback j j hb' = _ from hB, show a.pullback i i ha = _ from hA]
  apply BoundedAlgHom.ext
  intro x
  exact map_iota (K := K) (L := K) (f.pullback i j hj) x

/-- The analytic projections along the identity, on the category of
compatible presentations before analytic localization. -/
def unitNaturalProjection :
    (compatibleFunctor K K : CompatibleAtlasPresentation.{u, max u w, w} K ⥤ _) ⟶ 𝟭 _ where
  app A := unitCompatibleMap K A.presentation
  naturality _ _ f := unitCompatibleMap_naturality K f

/-- The projection along the identity becomes a natural isomorphism after
saturation and passage to the localized analytic category. -/
def unitIsoAfterSaturation :
    (compatibleFunctor K K : CompatibleAtlasPresentation.{u, max u w, max u w} K ⥤ _) ⋙
        CompatibleAtlasPresentation.saturationFunctor ⋙ SaturatedAtlasPresentation.localizationFunctor ≅
      CompatibleAtlasPresentation.saturationFunctor ⋙ SaturatedAtlasPresentation.localizationFunctor := by
  let F := CompatibleAtlasPresentation.saturationFunctor (K := K)
  let L := SaturatedAtlasPresentation.localizationFunctor (K := K)
  let τ := unitNaturalProjection.{u, max u w} K
  refine NatIso.ofComponents (fun A =>
    SaturatedAtlasPresentation.localizedQuasiIso (F.map (τ.app A))
      ((CompatibleAtlasPresentation.quasiIsomorphisms_saturationFunctor_map_iff
        (τ.app A)).mpr (unitCompatibleMap_isQuasiIso K A.presentation))) ?_
  intro A B f
  change (F ⋙ L).map ((compatibleFunctor K K).map f) ≫ (F ⋙ L).map (τ.app B) =
    (F ⋙ L).map (τ.app A) ≫ (F ⋙ L).map f
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (F ⋙ L).map (τ.naturality f)

/-- On saturated presentations, scalar extension along the identity agrees
with the ordinary localization functor. -/
def saturatedUnitIso :
    (saturatedLocalizedFunctor K K :
      SaturatedAtlasPresentation.{u, max u w, max u w} K ⥤ _) ≅
        SaturatedAtlasPresentation.localizationFunctor := by
  let F := SaturatedAtlasPresentation.compatibleFunctor (K := K)
  let H := CompatibleAtlasPresentation.saturationFunctor (K := K)
  let L := SaturatedAtlasPresentation.localizationFunctor (K := K)
  exact Functor.isoWhiskerLeft F (unitIsoAfterSaturation.{u, w} K) ≪≫
    (Functor.associator F H L).symm ≪≫
    Functor.isoWhiskerRight (SaturatedAtlasPresentation.saturationComparisonNatIso (K := K)) L ≪≫
    Functor.leftUnitor L

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
