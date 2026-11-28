import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionPoints
import Langlands.Geometry.Analytic.GroundFieldExtensionProjectionProper
import Langlands.Geometry.Analytic.SaturatedRightFractionComposition

/-! # Compatible points under analytic ground field extension -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open CategoryTheory Set Topology SaturatedAtlasPresentation
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

private theorem exists_chartwisePoint {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (f : CompatibleStrongHom A B) (y : A.space) (x : (chartSystem K L B.atlas).Space)
    (h : f.baseMap y = projection K L B.atlas x) :
    ∃ z : (chartSystem K L A.atlas).Space, projection K L A.atlas z = y ∧
      pointMap K L f.toStrongHom f.compatible z = x := by
  obtain ⟨i, s, rfl⟩ := mem_iUnion.mp
    (A.atlas.isNet_chartFamily.1.covers.symm ▸ mem_univ y)
  obtain ⟨j, hj⟩ := f.toStrongHom.target_exists i
  have hx : x ∈ range ((chartSystem K L B.atlas).chart j) := by
    rw [range_chart]
    change projection K L B.atlas x ∈ range (B.atlas.chart j)
    rw [← h]
    exact hj ⟨_, ⟨s, rfl⟩, rfl⟩
  obtain ⟨t, rfl⟩ := hx
  have hst : BanachSpectrum.comap (f.pullback i j hj).toBoundedRingHom s =
      spectrumProjection K L (B.atlas.algebra j) t := by
    apply (B.atlas.isEmbedding_chart j).injective
    rw [f.toStrongHom.chart_comm i j hj, ← projection_chart]
    exact h
  obtain ⟨r, hr, hr'⟩ := exists_spectrumPoint K L (f.pullback i j hj) s t hst
  refine ⟨(chartSystem K L A.atlas).chart i r, ?_, ?_⟩
  · rw [projection_chart, hr]
  · rw [pointMap_chart K L f.toStrongHom f.compatible i j hj, chartMap, hr']

private theorem exists_strongPoint {A B : SaturatedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (y : A.presentation.space)
    (x : localizedSpaceFunctor.obj ((localizedFunctor K L).obj (localizationFunctor.obj B)))
    (h : f.baseMap y = pointProjection K L (localizationFunctor.obj B) x) :
    ∃ z : localizedSpaceFunctor.obj ((localizedFunctor K L).obj (localizationFunctor.obj A)),
      pointProjection K L (localizationFunctor.obj A) z = y ∧
      localizedSpaceFunctor.map ((localizedFunctor K L).map (localizationFunctor.map f)) z = x := by
  let g := (SaturatedAtlasPresentation.compatibleFunctor (K := K)).map f
  obtain ⟨z, hz, hx⟩ := exists_chartwisePoint K L g y x h
  refine ⟨z, hz, ?_⟩
  rw [localizedFunctor_map]
  unfold saturatedLocalizedFunctor
  simp only [Functor.comp_map]
  exact hx

/-- The continuous comparison from the extended source to the pairs of
points with equal images in the original target. -/
def pointComparison {X Y : LocalizedCategory.{u, v, w} (K := K)} (f : X ⟶ Y) :
    C(localizedSpaceFunctor.obj ((localizedFunctor K L).obj X),
      {p : localizedSpaceFunctor.obj X × localizedSpaceFunctor.obj ((localizedFunctor K L).obj Y) //
        localizedSpaceFunctor.map f p.1 = pointProjection K L Y p.2}) where
  toFun z := ⟨⟨pointProjection K L X z, localizedSpaceFunctor.map ((localizedFunctor K L).map f) z⟩,
    (pointProjection_naturality K L f z).symm⟩
  continuous_toFun := ((pointProjection K L X).continuous.prodMk
    (localizedSpaceFunctor.map ((localizedFunctor K L).map f)).hom.continuous).subtype_mk _

/-- A point of the original source and a point of the extended target over
the same original target point lift to the extended source. -/
theorem exists_localizedPoint {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (f : X ⟶ Y)
    (y : localizedSpaceFunctor.obj X) (x : localizedSpaceFunctor.obj ((localizedFunctor K L).obj Y))
    (h : localizedSpaceFunctor.map f y = pointProjection K L Y x) :
    ∃ z : localizedSpaceFunctor.obj ((localizedFunctor K L).obj X), pointProjection K L X z = y ∧
      localizedSpaceFunctor.map ((localizedFunctor K L).map f) z = x := by
  obtain ⟨A, hA⟩ := (localizedObjectEquiv (K := K)).surjective X
  obtain ⟨B, hB⟩ := (localizedObjectEquiv (K := K)).surjective Y
  change localizationFunctor.obj A = X at hA
  change localizationFunctor.obj B = Y at hB
  subst X Y
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  let y₀ := φ.hs.inverseBaseMap y
  have h₀ : φ.f.baseMap y₀ = pointProjection K L (localizationFunctor.obj B) x := by
    rw [localizedSpaceFunctor_map_rightFraction] at h
    exact h
  obtain ⟨z, hz, hx⟩ := exists_strongPoint K L φ.f y₀ x h₀
  refine ⟨localizedSpaceFunctor.map ((localizedFunctor K L).map (localizationFunctor.map φ.s)) z, ?_, ?_⟩
  · rw [pointProjection_naturality, hz, localizedSpaceFunctor_map]
    exact φ.hs.1.homeomorph.apply_symm_apply y
  · have hφ := congrArg (localizedFunctor K L).map (localizationFunctor_map_s_comp_localizedRightFraction φ)
    rw [Functor.map_comp] at hφ
    have hmap := congrArg localizedSpaceFunctor.map hφ
    rw [Functor.map_comp] at hmap
    exact (congrArg (fun g => g z) hmap).trans hx

/-- The analytic comparison is surjective on all compatible point pairs. -/
theorem pointComparison_surjective {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (f : X ⟶ Y) : Function.Surjective (pointComparison K L f) := by
  rintro ⟨⟨y, x⟩, h⟩
  obtain ⟨z, hz, hx⟩ := exists_localizedPoint K L f y x h
  exact ⟨z, Subtype.ext (Prod.ext hz hx)⟩

/-- Ground field extension pulls back the image of any set of source points
to the image of its inverse image in the extended source. -/
theorem pointProjection_preimage_image {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (f : X ⟶ Y)
    (S : Set (localizedSpaceFunctor.obj X)) :
    pointProjection K L Y ⁻¹' (localizedSpaceFunctor.map f '' S) =
      localizedSpaceFunctor.map ((localizedFunctor K L).map f) '' (pointProjection K L X ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨z, hz, hzx⟩ := exists_localizedPoint K L f y x h
    exact ⟨z, show pointProjection K L X z ∈ S by rwa [hz], hzx⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨pointProjection K L X z, hz, (pointProjection_naturality K L f z).symm⟩

variable {X : LocalizedCategory.{u, v, w} (K := K)}

/-- Each original chart has a retained extended chart in the saturated
presentation of the scalar extension. -/
def extendedChart (i : (localizedObjectEquiv.symm X).presentation.atlas.Index) :
    (localizedObjectEquiv.symm ((localizedFunctor K L).obj X)).presentation.atlas.Index :=
  (IndexedAffinoidAtlas.GroundFieldExtension.atlas K L
    (localizedObjectEquiv.symm X).presentation.atlas).originalSaturatedIndex i

/-- The retained chart is the full inverse image of the original chart. -/
theorem range_extendedChart (i : (localizedObjectEquiv.symm X).presentation.atlas.Index) :
    range ((localizedObjectEquiv.symm ((localizedFunctor K L).obj X)).presentation.atlas.chart
      (extendedChart K L i)) =
      pointProjection K L X ⁻¹' range ((localizedObjectEquiv.symm X).presentation.atlas.chart i) := by
  obtain ⟨A, hA⟩ := (localizedObjectEquiv (K := K)).surjective X
  change localizationFunctor.obj A = X at hA
  subst X
  let a := A.presentation.atlas
  let b := IndexedAffinoidAtlas.GroundFieldExtension.atlas K L a
  change range (b.saturatedAtlas.chart (b.originalSaturatedIndex i)) =
    projection K L a ⁻¹' range (a.chart i)
  exact (b.saturatedAtlas_original_range i).trans (range_chart K L a i)

variable {ι : Type*} {Y : ι → LocalizedCategory.{u, v, w} (K := K)}

/-- The pullback of a union of images along the scalar-extension projection
is the union of the corresponding images after scalar extension. -/
theorem pointProjection_preimage_iUnion_image (f : ∀ i, Y i ⟶ X)
    (S : ∀ i, Set (localizedSpaceFunctor.obj (Y i))) :
    pointProjection K L X ⁻¹' (⋃ i, localizedSpaceFunctor.map (f i) '' S i) =
      ⋃ i, localizedSpaceFunctor.map ((localizedFunctor K L).map (f i)) ''
        (pointProjection K L (Y i) ⁻¹' S i) := by
  simp only [preimage_iUnion, pointProjection_preimage_image]

/-- A family is jointly surjective on analytic points exactly when its
scalar extension is jointly surjective. -/
theorem iUnion_range_eq_univ_after_extension_iff (f : ∀ i, Y i ⟶ X) :
    (⋃ i, range (localizedSpaceFunctor.map ((localizedFunctor K L).map (f i)))) = univ ↔
      (⋃ i, range (localizedSpaceFunctor.map (f i))) = univ := by
  have hpre := pointProjection_preimage_iUnion_image K L f (fun _ => univ)
  simp only [preimage_univ, image_univ] at hpre
  rw [← hpre, ← preimage_univ (f := pointProjection K L X)]
  exact (pointProjection_surjective K L X).preimage_injective.eq_iff

/-- A union of images of source charts that is a neighbourhood downstairs
remains a neighbourhood after scalar extension. For a finite family of
charts this transports the finite chart-neighbourhood condition. -/
theorem iUnion_chartImages_mem_nhds_after_extension (f : ∀ i, Y i ⟶ X)
    (c : ∀ i, (localizedObjectEquiv.symm (Y i)).presentation.atlas.Index)
    (x : localizedSpaceFunctor.obj ((localizedFunctor K L).obj X))
    (h : (⋃ i, localizedSpaceFunctor.map (f i) ''
      range ((localizedObjectEquiv.symm (Y i)).presentation.atlas.chart (c i))) ∈
        𝓝 (pointProjection K L X x)) :
    (⋃ i, localizedSpaceFunctor.map ((localizedFunctor K L).map (f i)) ''
      range ((localizedObjectEquiv.symm ((localizedFunctor K L).obj (Y i))).presentation.atlas.chart
        (extendedChart K L (c i)))) ∈ 𝓝 x := by
  have hpre := (pointProjection K L X).continuous.continuousAt.preimage_mem_nhds h
  rw [pointProjection_preimage_iUnion_image K L f] at hpre
  convert hpre using 1
  apply iUnion_congr
  intro i
  exact congrArg (fun S => localizedSpaceFunctor.map ((localizedFunctor K L).map (f i)) '' S)
    (range_extendedChart K L (X := Y i) (c i))

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
