import Langlands.Geometry.Analytic.AnalytificationCenterStatement
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormStatement

/-! # Center kernels, rational fibres, and the reduction to affine charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification.CenterComparison

open Langlands.AlgebraicGeometry.PointTopology
open PresentedAffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

theorem pointSeminorm_analyticPoint (φ : AlgPoint K A K) (a : A) :
    pointSeminorm K P (analyticPoint K P φ) a = ‖φ a‖ := by
  rw [analyticPoint, pointSeminorm_chart, chartSeminorm_apply, spectrumPoint_apply,
    character_algebraMap]

theorem mem_center_analyticPoint (φ : AlgPoint K A K) (a : A) :
    a ∈ (center K P (analyticPoint K P φ)).asIdeal ↔ φ a = 0 := by
  rw [center_asIdeal, mem_kernel, pointSeminorm_analyticPoint, norm_eq_zero]

theorem seminorm_eq_of_sub_eq_zero (ν : MulRingSeminorm A) {a b : A}
    (h : ν (a - b) = 0) : ν a = ν b := by
  apply le_antisymm
  · have hle := map_add_le_add ν (a - b) b
    simpa [h] using hle
  · have hle := map_add_le_add ν (b - a) a
    have h' : ν (b - a) = 0 := by
      rw [← neg_sub a b, map_neg_eq_map, h]
    simpa [h'] using hle

theorem pointSeminorm_eq_of_center_eq (φ : AlgPoint K A K) (x : Space K P)
    (h : center K P x = center K P (analyticPoint K P φ)) :
    pointSeminorm K P x = pointSeminorm K P (analyticPoint K P φ) := by
  ext a
  have hd : a - algebraMap K A (φ a) ∈ (center K P x).asIdeal := by
    rw [h, mem_center_analyticPoint]
    change φ.toAlgHom (a - algebraMap K A (φ.toAlgHom a)) = 0
    simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [center_asIdeal, mem_kernel] at hd
  calc
    pointSeminorm K P x a =
        pointSeminorm K P x (algebraMap K A (φ a)) :=
      seminorm_eq_of_sub_eq_zero (pointSeminorm K P x) hd
    _ = ‖φ a‖ := pointSeminorm_extendsNorm K P x (φ a)
    _ = pointSeminorm K P (analyticPoint K P φ) a :=
      (pointSeminorm_analyticPoint K P φ a).symm

theorem eq_analyticPoint_of_center_eq
    (hinj : Function.Injective (pointSeminorm K P))
    (φ : AlgPoint K A K) (x : Space K P)
    (h : center K P x = center K P (analyticPoint K P φ)) :
    x = analyticPoint K P φ :=
  hinj (pointSeminorm_eq_of_center_eq K P φ x h)

end Langlands.Analytic.AffineAnalytification.CenterComparison

namespace Langlands.Analytic.SchemeAnalytification.CenterComparison

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification
open Langlands.AlgebraicGeometry.PointTopology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

theorem affineOpenMap_injective (U : X.affineOpens) :
    Function.Injective (affineOpenMap U) := by
  let : IsAffine (U : Scheme) := U.property
  unfold affineOpenMap
  exact ((U : X.Opens).toScheme.isoSpec.inv ≫ (U : X.Opens).ι).isOpenEmbedding.injective

theorem localCenterPoint_localAnalyticPoint (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    localCenterPoint K f U (localAnalyticPoint K f U q) =
      (q.left ≫ (U : X.Opens).toScheme.isoSpec.hom) (IsLocalRing.closedPoint K) := by
  let : IsAffine (openOver K (Over.mk f) U.val).left := U.property
  have hs := affineSchemePointEquiv_spec K K q
  have he : CommRingCat.ofHom (affineAlgPoint K f U q).toAlgHom.toRingHom =
      CommRingCat.ofHom (affineSchemePointEquiv K
        (openOver K (Over.mk f) U.val) K q).toAlgHom.toRingHom := by
    rfl
  change localCenterPoint K f U (localAnalyticPoint K f U q) =
    (q.left ≫ (openOver K (Over.mk f) U.val).left.isoSpec.hom) (IsLocalRing.closedPoint K)
  rw [← hs, ← he]
  have hc : AffineAnalytification.center K (chartPresentation K f U)
      (AffineAnalytification.analyticPoint K (chartPresentation K f U)
        (affineAlgPoint K f U q)) =
      PrimeSpectrum.comap (affineAlgPoint K f U q).toAlgHom.toRingHom
        (IsLocalRing.closedPoint K) := by
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro a
    rw [AffineAnalytification.CenterComparison.mem_center_analyticPoint]
    change _ ↔ (affineAlgPoint K f U q) a ∈ (IsLocalRing.closedPoint K).asIdeal
    simp [IsLocalRing.closedPoint]
  exact hc

theorem localCenter_localAnalyticPoint (U : X.affineOpens)
    (q : RingPoint K (openOver K (Over.mk f) U.val) K) :
    localCenter K f U (localAnalyticPoint K f U q) =
      (openPointMap K (Over.mk f) K U.val q).left (IsLocalRing.closedPoint K) := by
  have hc := congrArg (affineOpenMap U) (localCenterPoint_localAnalyticPoint K f U q)
  change localCenter K f U (localAnalyticPoint K f U q) = _ at hc
  rw [hc]
  let g : Spec (CommRingCat.of K) ⟶ (U : X.Opens).toScheme := q.left
  have he : (g ≫ (U : X.Opens).toScheme.isoSpec.hom) ≫
      ((U : X.Opens).toScheme.isoSpec.inv ≫ (U : X.Opens).ι) =
      g ≫ (U : X.Opens).ι := by
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun g : Spec (CommRingCat.of K) ⟶ X =>
    g (IsLocalRing.closedPoint K)) he

theorem center_analyticRationalPoint (p : RingPoint K (Over.mk f) K) :
    center K f (analyticRationalPoint K f p) = p.left (IsLocalRing.closedPoint K) := by
  rw [analyticRationalPoint_def, center_ι, localCenter_localAnalyticPoint,
    openPointMap_pointLift]

theorem center_surjective_of_affine
    (hsurj : ∀ U : X.affineOpens,
      Function.Surjective (AffineAnalytification.center K (chartPresentation K f U))) :
    Function.Surjective (center K f) := by
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x)
    (U := ⊤) (by trivial)
  let V : X.affineOpens := ⟨U, hU⟩
  let : IsAffine U.toScheme := hU
  let y : PrimeSpectrum (CoordinateRing (structureMap f V)) :=
    U.toScheme.isoSpec.hom ⟨x, hx⟩
  obtain ⟨z, hz⟩ := hsurj V y
  refine ⟨ι K f V z, ?_⟩
  have hc : localCenterPoint K f V z = y := hz
  rw [center_ι, localCenter_apply, hc]
  change (U.toScheme.isoSpec.inv ≫ U.ι) (U.toScheme.isoSpec.hom ⟨x, hx⟩) = x
  exact congrArg (fun g : U.toScheme ⟶ X => g ⟨x, hx⟩)
    (U.toScheme.isoSpec.hom_inv_id_assoc U.ι)

theorem eq_analyticRationalPoint_of_center_eq
    (hrange : ∀ U : X.affineOpens,
      center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U))
    (hinj : ∀ U : X.affineOpens,
      Function.Injective (AffineAnalytification.pointSeminorm K (chartPresentation K f U)))
    (p : RingPoint K (Over.mk f) K) (z : Space K f)
    (h : center K f z = center K f (analyticRationalPoint K f p)) :
    z = analyticRationalPoint K f p := by
  let U := pointAffine K f p
  have hz : z ∈ Set.range (ι K f U) := by
    rw [← hrange U]
    change center K f z ∈ (U : X.Opens)
    rw [h, analyticRationalPoint_def, center_ι]
    exact center_ι_mem K f U (localAnalyticPoint K f U (pointLift K f p))
  obtain ⟨w, rfl⟩ := hz
  have hc : AffineAnalytification.center K (chartPresentation K f U) w =
      AffineAnalytification.center K (chartPresentation K f U)
        (localAnalyticPoint K f U (pointLift K f p)) := by
    apply affineOpenMap_injective U
    change localCenter K f U w =
      localCenter K f U (localAnalyticPoint K f U (pointLift K f p))
    exact h
  have hw := AffineAnalytification.CenterComparison.eq_analyticPoint_of_center_eq
    K (chartPresentation K f U) (hinj U) (affineAlgPoint K f U (pointLift K f p)) w hc
  rw [hw]
  rfl

end Langlands.Analytic.SchemeAnalytification.CenterComparison
