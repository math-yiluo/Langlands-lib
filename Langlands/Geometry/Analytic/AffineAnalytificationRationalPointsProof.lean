import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm
import Langlands.Geometry.Analytic.FieldPointSaturation

/-! # Proof: rational points of the polynomial-locus analytification -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open Set Topology Filter PresentedAffinoidAlgebra AnalyticAffineSpace
open Langlands.AlgebraicGeometry.PointTopology AffinoidAtlasPresentation

namespace RationalPointComparison

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A base-field-valued point of any atlas is determined by its underlying point. -/
theorem fieldPoint_point_injective {X : AffinoidAtlasPresentation.{u, v, w} K} :
    Function.Injective (FieldPoint.point : FieldPoint K X → X.space) :=
  fun _ _ h => FieldPointSaturationComparison.fieldPoint_ext h

/-- The point-realizing evaluation has norm bound one. -/
def boundedEval {X : AffinoidAtlasPresentation.{u, v, w} K} (p : FieldPoint K X)
    (i : X.atlas.Index) (hi : p.point ∈ range (X.atlas.chart i)) :
    BoundedAlgHom K (X.atlas.algebra i) K where
  toAlgHom := p.eval i hi
  bounded := by
    obtain ⟨s, -, hn⟩ := p.isChartPoint i hi
    exact ⟨1, zero_lt_one, fun b => by
      change ‖p.eval i hi b‖ ≤ 1 * ‖b‖
      rw [one_mul, hn b]
      exact s.le_norm b⟩

variable (K) {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- A chart containing a field point admits the recovered algebraic point. -/
theorem radiusAdmits_toAlgPoint (p : FieldPoint K (presentation K P))
    (i : (presentation K P).atlas.Index)
    (hi : p.point ∈ range ((presentation K P).atlas.chart i)) :
    RadiusAdmits K P (toAlgPoint K P p) i.val := by
  obtain ⟨s, -, hn⟩ := p.isChartPoint i hi
  intro j
  have he : pointCoordinates K P (toAlgPoint K P p) j =
      p.eval i hi (coordinate K (algebra K P i.val) j) := by
    rw [pointCoordinates, toAlgPoint_apply_eq K P p i hi]
    change p.eval i hi (PolynomialLocus.algebraMap P _ (P.map (MvPolynomial.X j))) = _
    rw [PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]
  rw [he]
  change ∀ b : algebra K P i.val, ‖p.eval i hi b‖ = s.toMulRingSeminorm b at hn
  rw [hn]
  exact (s.le_norm _).trans (norm_coordinate_le K (algebra K P i.val) j)

/-- Coordinates determine the bounded character of the recovered algebraic point. -/
theorem character_toAlgPoint (p : FieldPoint K (presentation K P))
    (i : (presentation K P).atlas.Index)
    (hi : p.point ∈ range ((presentation K P).atlas.chart i)) :
    character K P (radiusAdmits_toAlgPoint K P p i hi) = boundedEval p i hi := by
  apply hom_ext_coordinate K K (algebra K P i.val)
  intro (j : Fin P.arity)
  change character K P (radiusAdmits_toAlgPoint K P p i hi)
    (coordinate K (algebra K P i.val) j) = p.eval i hi _
  rw [character_coordinate K P (radiusAdmits_toAlgPoint K P p i hi) j]
  rw [pointCoordinates, toAlgPoint_apply_eq K P p i hi]
  change p.eval i hi (PolynomialLocus.algebraMap P _ (P.map (MvPolynomial.X j))) = _
  rw [PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

/-- The recovered algebraic point has the original analytic point. -/
theorem analyticPoint_toAlgPoint (p : FieldPoint K (presentation K P)) :
    analyticPoint K P (toAlgPoint K P p) = p.point := by
  let i := chosenChart K P p
  have hi := mem_range_chosenChart K P p
  obtain ⟨s, hs, hn⟩ := p.isChartPoint i hi
  rw [← chart_spectrumPoint K P (radiusAdmits_toAlgPoint K P p i hi)]
  have he : spectrumPoint K P (radiusAdmits_toAlgPoint K P p i hi) = s := by
    apply BanachSpectrum.ext
    intro b
    rw [spectrumPoint_apply, character_toAlgPoint]
    exact hn b
  rw [he]
  exact hs

theorem toFieldPoint_toAlgPoint (p : FieldPoint K (presentation K P)) :
    toFieldPoint K P (toAlgPoint K P p) = p :=
  fieldPoint_point_injective (analyticPoint_toAlgPoint K P p)

theorem toFieldPoint_bijective : Function.Bijective (toFieldPoint K P) :=
  ⟨Function.LeftInverse.injective (toAlgPoint_toFieldPoint K P),
    fun p => ⟨toAlgPoint K P p, toFieldPoint_toAlgPoint K P p⟩⟩

/-- The seminorm of an algebraic point is its evaluation absolute value. -/
theorem pointSeminorm_analyticPoint_apply (φ : AlgPoint K A K) (a : A) :
    pointSeminorm K P (analyticPoint K P φ) a = ‖φ a‖ := by
  rw [analyticPoint, pointSeminorm_chart, chartSeminorm_apply,
    spectrumPoint_apply, character_algebraMap]

theorem analyticPoint_injective : Function.Injective (analyticPoint K P) := by
  intro φ ψ h
  apply (toFieldPoint_bijective K P).injective
  exact fieldPoint_point_injective h

/-- The seminorm topology on the analytification induces the evaluation topology
on its algebraic points. Translated evaluations recover every norm ball in `K`. -/
theorem isEmbedding_analyticPoint_of_seminorm
    (h : IsEmbedding (fun (x : Space K P) (a : A) => pointSeminorm K P x a)) :
    IsEmbedding (analyticPoint K P) := by
  have hc : Continuous (analyticPoint K P) := h.continuous_iff.mpr (by
    apply continuous_pi
    intro a
    simpa only [Function.comp_apply, pointSeminorm_analyticPoint_apply] using
      (AlgPoint.continuous_eval (R := K) (S := K) a).norm)
  refine ⟨⟨le_antisymm hc.le_induced ?_⟩, analyticPoint_injective K P⟩
  have he : Continuous[TopologicalSpace.induced (analyticPoint K P) inferInstance,
      inferInstance] (AlgPoint.evaluation : AlgPoint K A K → A → K) := by
    let : TopologicalSpace (AlgPoint K A K) :=
      TopologicalSpace.induced (analyticPoint K P) inferInstance
    apply continuous_pi
    intro a
    apply continuous_iff_continuousAt.mpr
    intro φ
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hval (ψ : AlgPoint K A K) :
        pointSeminorm K P (analyticPoint K P ψ) (a - algebraMap K A (φ a)) =
          ‖ψ a - φ a‖ := by
      rw [pointSeminorm_analyticPoint_apply]
      change ‖ψ.toAlgHom (a - algebraMap K A (φ a))‖ = _
      rw [map_sub, AlgHom.commutes]
      rfl
    have ht := ((continuous_pointSeminorm_apply K P (a - algebraMap K A (φ a))).comp
      (continuous_induced_dom : Continuous (analyticPoint K P))).tendsto φ
    have hfun : (fun x : Space K P => pointSeminorm K P x
        (a - algebraMap K A (φ a))) ∘ analyticPoint K P =
          (fun ψ : AlgPoint K A K => ‖ψ a - φ a‖) := funext hval
    rw [hfun] at ht
    simpa only [AlgPoint.evaluation, sub_self, norm_zero] using ht
  exact he.le_induced

namespace SeminormTopology

/-- A spectrum point is a 1-Lipschitz function on its algebra. -/
theorem continuous_spectrum_apply {B : Type*} [NormedCommRing B] (s : BanachSpectrum B) :
    Continuous (fun b : B => s b) :=
  (LipschitzWith.of_le_add fun a b => by
    rw [dist_eq_norm]
    have h := map_add_le_add s.toMulRingSeminorm b (a - b)
    rw [add_sub_cancel] at h
    exact h.trans (add_le_add le_rfl (s.le_norm (a - b)))).continuous

omit [CompleteSpace K] in
theorem denseRange_chartAlgebraMap (m : ℕ) :
    DenseRange (PolynomialLocus.algebraMap P (polyradius K P.arity m)) := by
  have h : DenseRange (PolynomialLocus.polynomialMap P (polyradius K P.arity m)) :=
    (presentationMap_surjective K (algebra K P m)).denseRange.comp
      (GeneralizedTateAlgebra.denseRange_polynomialMap (polyradius K P.arity m) K)
      (presentationMap K (algebra K P m)).continuous
  refine Dense.mono ?_ h
  rintro _ ⟨p, rfl⟩
  exact ⟨P.map p, PolynomialLocus.algebraMap_map P _ p⟩

omit [CompleteSpace K] in
theorem chartSeminorm_injective (m : ℕ) : Function.Injective (chartSeminorm K P m) := by
  intro s t h
  apply BanachSpectrum.ext
  intro b
  have e := Continuous.ext_on (denseRange_chartAlgebraMap K P m)
    (continuous_spectrum_apply s) (continuous_spectrum_apply t) (by
      rintro _ ⟨a, rfl⟩
      exact congrArg (fun ν : MulRingSeminorm A => ν a) h)
  exact congrFun e b

theorem pointSeminorm_injective : Function.Injective (pointSeminorm K P) := by
  intro x y h
  obtain ⟨m, s, rfl⟩ := exists_chart K P x
  obtain ⟨k, t, rfl⟩ := exists_chart K P y
  rw [← chart_pull K P (le_max_left m k) s, ← chart_pull K P (le_max_right m k) t] at h ⊢
  rw [pointSeminorm_chart, pointSeminorm_chart] at h
  rw [chartSeminorm_injective K P _ h]

theorem coordinateNorm_eq (i : Fin P.arity) (z : Space K P) :
    coordinateNorm K P i z = pointSeminorm K P z (P.map (MvPolynomial.X i)) := by
  obtain ⟨m, s, rfl⟩ := exists_chart K P z
  rw [coordinateNorm_chart, pointSeminorm_chart, chartSeminorm_apply,
    PolynomialLocus.algebraMap_map, PolynomialLocus.polynomialMap_X]

theorem isEmbedding_pointSeminorm :
    IsEmbedding (fun (x : Space K P) (a : A) => pointSeminorm K P x a) := by
  set Φ := fun (x : Space K P) (a : A) => pointSeminorm K P x a with hΦ
  have hΦc : Continuous Φ := continuous_pi fun a => continuous_pointSeminorm_apply K P a
  have hΦi : Function.Injective Φ := fun x y h =>
    pointSeminorm_injective K P (MulRingSeminorm.ext fun a => congrFun h a)
  refine ⟨?_, hΦi⟩
  rw [isInducing_iff_nhds]
  intro x
  refine le_antisymm (hΦc.tendsto x).le_comap ?_
  intro U hU
  obtain ⟨m, s, rfl⟩ := exists_chart K P x
  have hx : chart K P m s ∈ openDisc K P m := range_chart_subset_openDisc K P m ⟨s, rfl⟩
  obtain ⟨t, ht⟩ := openDisc_subset_range_chart K P m hx
  have hg : IsClosedEmbedding (Φ ∘ chart K P (m + 1)) :=
    (hΦc.comp (continuous_chart K P (m + 1))).isClosedEmbedding
      (hΦi.comp (isClosedEmbedding_chart K P (m + 1)).injective)
  have hU' : chart K P (m + 1) ⁻¹' U ∈ 𝓝 t :=
    (continuous_chart K P (m + 1)).continuousAt.preimage_mem_nhds (by rw [ht]; exact hU)
  rw [hg.isInducing.nhds_eq_comap t] at hU'
  obtain ⟨V, hV, hVU⟩ := hU'
  let W : Set (A → ℝ) := {f | ∀ i, f (P.map (MvPolynomial.X i)) < radius K (m + 1)}
  have hW : IsOpen W := by
    have e : W = ⋂ i, {f : A → ℝ | f (P.map (MvPolynomial.X i)) < radius K (m + 1)} := by
      ext f
      simp [W]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply _) continuous_const
  have hxW : Φ (chart K P m s) ∈ W := fun i => by
    have := hx i
    rw [coordinateNorm_eq] at this
    exact this
  have hV' : V ∈ 𝓝 (Φ (chart K P m s)) := by
    rw [Function.comp_apply, ht] at hV
    exact hV
  refine Filter.mem_comap.mpr ⟨V ∩ W, inter_mem hV' (hW.mem_nhds hxW), ?_⟩
  rintro z ⟨hzV, hzW⟩
  have hzD : z ∈ openDisc K P m := fun i => by
    rw [coordinateNorm_eq]
    exact hzW i
  obtain ⟨u, rfl⟩ := openDisc_subset_range_chart K P m hzD
  exact hVU hzV

end SeminormTopology

/-- Algebraic points embed topologically into the constructed analytification. -/
theorem isEmbedding_analyticPoint : IsEmbedding (analyticPoint K P) :=
  isEmbedding_analyticPoint_of_seminorm K P (SeminormTopology.isEmbedding_pointSeminorm K P)

/-- The equivalence with the base-field-valued points of the saturated atlas. -/
def saturatedFieldPointEquiv : AlgPoint K A K ≃ FieldPoint K (saturated K P).presentation :=
  (Equiv.ofBijective (toFieldPoint K P) (toFieldPoint_bijective K P)).trans
    (FieldPointSaturationComparison.saturationEquiv (presentation K P))

@[simp]
theorem saturatedFieldPointEquiv_point (φ : AlgPoint K A K) :
    (saturatedFieldPointEquiv K P φ).point = analyticPoint K P φ := rfl

end RationalPointComparison

/-- The rational-point comparison, including the evaluation topology and atlas saturation. -/
theorem affineAnalytificationRationalPoints :
    AffineAnalytificationRationalPointsStatement.{u, v} := by
  intro K _ _ _ A _ _ P
  exact ⟨RationalPointComparison.toFieldPoint_bijective K P,
    RationalPointComparison.isEmbedding_analyticPoint K P,
    RationalPointComparison.saturatedFieldPointEquiv K P,
    RationalPointComparison.saturatedFieldPointEquiv_point K P⟩

end Langlands.Analytic.AffineAnalytification
