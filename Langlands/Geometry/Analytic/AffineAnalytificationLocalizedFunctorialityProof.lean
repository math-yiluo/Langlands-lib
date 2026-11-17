import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityStatement
import Langlands.Geometry.Analytic.DirectedAtlasComposition
import Langlands.Geometry.Analytic.CompatibleStrongSaturationFunctor

/-! # Functoriality and presentation independence of affine analytification -/

noncomputable section

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory AffinoidAtlasPresentation

namespace LocalizedFunctorialityComparison

namespace OriginalStrongMaps

open Set PresentedAffinoidAlgebra AnalyticAffineSpace

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-! ## Coordinates of the polynomial-locus charts -/

omit [CompleteSpace K] in
/-- The coordinates of a chart algebra are the images of the generators of `A`. -/
theorem coordinate_eq_algebraMap (m : ℕ) (t : Fin P.arity) :
    coordinate K (algebra K P m) t =
      PolynomialLocus.algebraMap P (polyradius K P.arity m) (P.map (MvPolynomial.X t)) := by
  rw [PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

/-- The restrictions of the constructed atlas send coordinates to coordinates. -/
theorem atlas_restriction_coordinate (i j : (presentation K P).atlas.Index)
    (h : range ((presentation K P).atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
    (t : Fin P.arity) :
    (presentation K P).atlas.restriction i j h (coordinate K (algebra K P j.val) t) =
      coordinate K (algebra K P i.val) t :=
  PolynomialLocus.restriction_coordinate P _ _ _ t

/-- The selected charts of the constructed atlas cover the analytification. -/
theorem exists_mem_range_chart (z : (presentation K P).space) :
    ∃ i, z ∈ range ((presentation K P).atlas.chart i) := by
  obtain ⟨m, s, rfl⟩ := exists_chart K P z
  refine ⟨representative K P m, ?_⟩
  change chart K P m s ∈ range (chart K P (representative K P m).val)
  rw [range_representative]
  exact mem_range_self s

/-- Two charts of the constructed atlas lie in a common chart. -/
theorem exists_common_chart (j j' : (presentation K P).atlas.Index) :
    ∃ q : (presentation K P).atlas.Index,
      range ((presentation K P).atlas.chart j) ⊆ range ((presentation K P).atlas.chart q) ∧
        range ((presentation K P).atlas.chart j') ⊆ range ((presentation K P).atlas.chart q) :=
  atlas_hasDirectedCharts K P j j'

/-! ## Strong maps into the constructed atlas -/

section Strong

variable {X : AffinoidAtlasPresentation.{u, u, 0} K}

/-- The coordinate values of the pullbacks of a strong map into the constructed atlas do
not depend on the admissible target chart. -/
theorem pullback_coordinate_eq (F : StrongHom X (presentation K P)) (i : X.atlas.Index)
    (j j' : (presentation K P).atlas.Index)
    (h : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
    (h' : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j'))
    (t : Fin P.arity) :
    F.pullback i j h (coordinate K (algebra K P j.val) t) =
      F.pullback i j' h' (coordinate K (algebra K P j'.val) t) := by
  obtain ⟨q, hjq, hj'q⟩ := exists_common_chart P j j'
  have hq : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q) :=
    h.trans hjq
  have c : F.pullback i q hq (coordinate K (algebra K P q.val) t) =
      F.pullback i j h (coordinate K (algebra K P j.val) t) := by
    rw [F.pullback_comp_restriction i j q hjq h hq]
    exact congrArg (F.pullback i j h) (atlas_restriction_coordinate P j q hjq t)
  have c' : F.pullback i q hq (coordinate K (algebra K P q.val) t) =
      F.pullback i j' h' (coordinate K (algebra K P j'.val) t) := by
    rw [F.pullback_comp_restriction i j' q hj'q h' hq]
    exact congrArg (F.pullback i j' h') (atlas_restriction_coordinate P j' q hj'q t)
  exact c.symm.trans c'

/-- A strong map into the constructed atlas is determined by the coordinate values of
one admissible pullback for each source chart. -/
theorem strongHom_eq_of_coordinate (F G : StrongHom X (presentation K P))
    (hcover : ∀ z : X.space, ∃ i, z ∈ range (X.atlas.chart i))
    (hp : ∀ i, ∃ (j : (presentation K P).atlas.Index)
      (hF : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j))
      (j' : (presentation K P).atlas.Index)
      (hG : G.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart j')),
      ∀ t : Fin P.arity, F.pullback i j hF (coordinate K (algebra K P j.val) t) =
        G.pullback i j' hG (coordinate K (algebra K P j'.val) t)) :
    F = G := by
  have hpb : ∀ i, ∃ (q : (presentation K P).atlas.Index)
      (hF : F.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q))
      (hG : G.baseMap '' range (X.atlas.chart i) ⊆ range ((presentation K P).atlas.chart q)),
      F.pullback i q hF = G.pullback i q hG := by
    intro i
    obtain ⟨j, hF, j', hG, h⟩ := hp i
    obtain ⟨q, hjq, hj'q⟩ := exists_common_chart P j j'
    have hFq : F.baseMap '' range (X.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q) := hF.trans hjq
    have hGq : G.baseMap '' range (X.atlas.chart i) ⊆
        range ((presentation K P).atlas.chart q) := hG.trans hj'q
    refine ⟨q, hFq, hGq, ?_⟩
    apply PresentedAffinoidAlgebra.hom_ext_coordinate
    intro t
    exact (pullback_coordinate_eq P F i q j hFq hF t).trans
      ((h t).trans (pullback_coordinate_eq P G i j' q hG hGq t))
  have hb : F.baseMap = G.baseMap := by
    ext z
    obtain ⟨i, y, rfl⟩ := hcover z
    obtain ⟨q, hF, hG, h⟩ := hpb i
    rw [← F.chart_comm i q hF y, ← G.chart_comm i q hG y, h]
  refine StrongHom.ext_of_directed (atlas_hasDirectedCharts K P) hb fun i => ?_
  obtain ⟨q, hF, hG, h⟩ := hpb i
  exact ⟨q, hF, h⟩

end Strong

/-! ## Pullbacks of the induced strong maps -/

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- Every admissible pullback of the strong map induced by `f` sends the coordinates to
the images of the generators under `f`. -/
theorem strongHom_pullback_coordinate (i : (presentation K Q).atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : (strongHom K P Q f).baseMap '' range ((presentation K Q).atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) (t : Fin P.arity) :
    (strongHom K P Q f).pullback i j h (coordinate K (algebra K P j.val) t) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val)
        (f (P.map (MvPolynomial.X t))) := by
  have e := StrongHom.ofDirected_pullback_selected (atlasHom K P Q f)
    (atlas_hasDirectedCharts K P) i
  have c : ∀ y, (strongHom K P Q f).pullback i ((atlasHom K P Q f).indexMap i)
      ((atlasHom K P Q f).image_chart_subset i) y = (atlasHom K P Q f).pullback i y := by
    intro y
    change (StrongHom.ofDirected (atlasHom K P Q f) (atlas_hasDirectedCharts K P)).pullback i
      ((atlasHom K P Q f).indexMap i) ((atlasHom K P Q f).image_chart_subset i) y = _
    rw [e]
  exact (pullback_coordinate_eq P (strongHom K P Q f) i j ((atlasHom K P Q f).indexMap i) h
    ((atlasHom K P Q f).image_chart_subset i) t).trans
      ((c _).trans ((pullback_coordinate K P Q f i t).trans
        (generatorValue_eq_algebraMap K P Q f i.val t)))

/-- Every admissible pullback of the strong map induced by `f` is compatible with the
coordinate-algebra maps and `f`. -/
theorem strongHom_pullback_algebraMap (i : (presentation K Q).atlas.Index)
    (j : (presentation K P).atlas.Index)
    (h : (strongHom K P Q f).baseMap '' range ((presentation K Q).atlas.chart i) ⊆
      range ((presentation K P).atlas.chart j)) (a : A) :
    (strongHom K P Q f).pullback i j h
        (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (f a) := by
  have hmaps : ((strongHom K P Q f).pullback i j h).toAlgHom.comp
      ((PolynomialLocus.algebraMap P (polyradius K P.arity j.val)).comp P.map) =
        ((PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val)).comp f).comp P.map := by
    apply MvPolynomial.algHom_ext
    intro t
    change (strongHom K P Q f).pullback i j h
        (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) (P.map (MvPolynomial.X t))) =
      PolynomialLocus.algebraMap Q (polyradius K Q.arity i.val) (f (P.map (MvPolynomial.X t)))
    exact (congrArg ((strongHom K P Q f).pullback i j h)
      (coordinate_eq_algebraMap P j.val t)).symm.trans
        (strongHom_pullback_coordinate P Q f i j h t)
  obtain ⟨p, rfl⟩ := P.surjective a
  exact AlgHom.congr_fun hmaps p

/-! ## The three clauses -/

/-- Clause 1: the identity of `A` induces the identity strong map. -/
theorem strongHom_id :
    strongHom K P P (AlgHom.id K A) = StrongHom.id (presentation K P) := by
  refine strongHom_eq_of_coordinate P _ _ (exists_mem_range_chart P) fun i => ?_
  refine ⟨(atlasHom K P P (AlgHom.id K A)).indexMap i,
    (atlasHom K P P (AlgHom.id K A)).image_chart_subset i, i,
    fun _ ⟨y, hy, e⟩ => e ▸ hy, fun t => ?_⟩
  exact (strongHom_pullback_coordinate P P (AlgHom.id K A) i _ _ t).trans
    ((coordinate_eq_algebraMap P i.val t).symm.trans
      (atlas_restriction_coordinate P i i subset_rfl t).symm)

variable {C : Type x} [CommRing C] [Algebra K C] (R : FinitePolynomialPresentation K C)
  (g : B →ₐ[K] C)

/-- Clause 2: the strong map induced by `g ∘ f` is the directed composite. -/
theorem strongHom_comp :
    strongHom K P R (g.comp f) =
      StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) := by
  refine strongHom_eq_of_coordinate P _ _ (exists_mem_range_chart R) fun i => ?_
  obtain ⟨j, hj⟩ := (strongHom K Q R g).target_exists i
  obtain ⟨k, hk⟩ := (strongHom K P Q f).target_exists j
  have hc : (StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
      (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P)).baseMap ''
        range ((presentation K R).atlas.chart i) ⊆ range ((presentation K P).atlas.chart k) :=
    StrongHom.comp_admissible (strongHom K Q R g) (strongHom K P Q f) i j k hj hk
  obtain ⟨j₀, h₀⟩ := (strongHom K P R (g.comp f)).target_exists i
  refine ⟨j₀, h₀, k, hc, fun t => ?_⟩
  have hr := StrongHom.compOfDirected_pullback (strongHom K Q R g) (strongHom K P Q f)
    (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) i j k hj hk hc
  refine (strongHom_pullback_coordinate P R (g.comp f) i j₀ h₀ t).trans ?_
  rw [hr]
  exact ((congrArg ((strongHom K Q R g).pullback i j hj)
      (strongHom_pullback_coordinate P Q f j k hk t)).trans
    (strongHom_pullback_algebraMap Q R g i j hj _)).symm

end OriginalStrongMaps

/-- Saturation extensions of equal strong maps are equal, whatever the coherence proofs. -/
theorem saturationExtension_congr {K : Type u} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {X Y : AffinoidAtlasPresentation.{u, v, w} K} {F G : StrongHom X Y}
    (e : F = G) (hF : F.HasCoherentPullbacks) (hG : G.HasCoherentPullbacks) :
    F.saturationExtension hF = G.saturationExtension hG := by
  subst e
  rfl

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {B : Type w} [CommRing B] [Algebra K B]
  (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The strong map induced by `f`, as a compatible strong map. -/
def compatibleHom : CompatibleStrongHom (presentation K Q) (presentation K P) where
  toStrongHom := strongHom K P Q f
  compatible := (strongHom K P Q f).hasLocallyCompatiblePullbacks_iff.mpr
    (strongHom_hasCoherentPullbacks K P Q f)

theorem saturatedHom_eq_compatible :
    saturatedHom K P Q f = (compatibleHom P Q f).saturationExtension :=
  rfl

/-- Assertion 1 from the identity clause of the affine functoriality statement. -/
theorem saturatedHom_id
    (hid : strongHom K P P (AlgHom.id K A) = StrongHom.id (presentation K P)) :
    saturatedHom K P P (AlgHom.id K A) = 𝟙 (saturated K P) :=
  (saturationExtension_congr hid (strongHom_hasCoherentPullbacks K P P (AlgHom.id K A))
    (StrongHom.hasCoherentPullbacks_id (presentation K P))).trans
    (CompatibleStrongHom.saturationExtension_id (presentation K P))

variable {C : Type x} [CommRing C] [Algebra K C] (R : FinitePolynomialPresentation K C)
  (g : B →ₐ[K] C)

/-- The directed composite of the induced strong maps is the compatible composite. -/
theorem compOfDirected_eq_comp :
    StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P) =
      ((compatibleHom Q R g).comp (compatibleHom P Q f)).toStrongHom := by
  refine StrongHom.ext_of_coherent
    (StrongHom.hasCoherentPullbacks_of_hasDirectedCharts _ (atlas_hasDirectedCharts K P))
    ((compatibleHom Q R g).comp (compatibleHom P Q f)).coherent rfl ?_
  intro i
  obtain ⟨j, hg⟩ := (strongHom K Q R g).target_exists i
  obtain ⟨k, hf⟩ := (strongHom K P Q f).target_exists j
  have h := StrongHom.comp_admissible (strongHom K Q R g) (strongHom K P Q f) i j k hg hf
  refine ⟨k, h, ?_⟩
  exact (StrongHom.compOfDirected_pullback _ _ _ _ i j k hg hf h).trans
    (CompatibleStrongHom.comp_pullback (compatibleHom Q R g) (compatibleHom P Q f)
      i j k hg hf _).symm

/-- Assertion 2 from the composition clause of the affine functoriality statement. -/
theorem saturatedHom_comp
    (hcomp : strongHom K P R (g.comp f) =
      StrongHom.compOfDirected (strongHom K Q R g) (strongHom K P Q f)
        (atlas_hasDirectedCharts K Q) (atlas_hasDirectedCharts K P)) :
    saturatedHom K P R (g.comp f) = saturatedHom K Q R g ≫ saturatedHom K P Q f :=
  (saturationExtension_congr (hcomp.trans (compOfDirected_eq_comp P Q f R g))
    (strongHom_hasCoherentPullbacks K P R (g.comp f))
    ((compatibleHom Q R g).comp (compatibleHom P Q f)).coherent).trans
    (CompatibleStrongHom.saturationExtension_comp (compatibleHom Q R g) (compatibleHom P Q f))

end LocalizedFunctorialityComparison

open LocalizedFunctorialityComparison

/-- Affine analytification respects identities and composition in the saturated and
localized categories, and its localized object is independent of the presentation. -/
theorem affineAnalytificationLocalizedFunctoriality :
    AffineAnalytificationLocalizedFunctorialityStatement.{u, v, w, x} := by
  intro K _ _ _ A _ _ B _ _ C _ _ P P' Q R f g
  have sid := saturatedHom_id P (OriginalStrongMaps.strongHom_id P)
  have scomp := saturatedHom_comp P Q f R g (OriginalStrongMaps.strongHom_comp P Q f R g)
  have lid : ∀ P₀ : FinitePolynomialPresentation K A,
      localizedHom K P₀ P₀ (AlgHom.id K A) = 𝟙 (localized K P₀) := by
    intro P₀
    change SaturatedAtlasPresentation.localizationFunctor.map _ = _
    rw [saturatedHom_id P₀ (OriginalStrongMaps.strongHom_id P₀)]
    exact SaturatedAtlasPresentation.localizationFunctor.map_id _
  have lcomp : ∀ P₀ P₁ : FinitePolynomialPresentation K A,
      localizedHom K P₀ P₁ (AlgHom.id K A) ≫ localizedHom K P₁ P₀ (AlgHom.id K A) =
        𝟙 (localized K P₁) := by
    intro P₀ P₁
    have e := saturatedHom_comp P₁ P₀ (AlgHom.id K A) P₁ (AlgHom.id K A)
      (OriginalStrongMaps.strongHom_comp P₁ P₀ (AlgHom.id K A) P₁ (AlgHom.id K A))
    rw [AlgHom.id_comp] at e
    have e' := congrArg (fun φ => SaturatedAtlasPresentation.localizationFunctor.map φ) e
    simp only [Functor.map_comp] at e'
    rw [← lid P₁]
    exact e'.symm
  refine ⟨sid, scomp, ?_, ?_, ?_⟩
  · exact lid P
  · change SaturatedAtlasPresentation.localizationFunctor.map _ = _
    rw [scomp]
    exact SaturatedAtlasPresentation.localizationFunctor.map_comp _ _
  · exact ⟨⟨localizedHom K P' P (AlgHom.id K A), lcomp P P', lcomp P' P⟩⟩

end Langlands.Analytic.AffineAnalytification
