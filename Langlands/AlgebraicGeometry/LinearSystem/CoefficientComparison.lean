import Langlands.AlgebraicGeometry.LinearSystem.LinearActionTwist
import Langlands.AlgebraicGeometry.LinearSystem.ChartFunctoriality
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.LinearAction

/-! # Linear systems and change of coefficient ring -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restricting the coefficient ring composes the actual map on global scalars. -/
lemma scalarsFromBase_specMap {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) (f : R ⟶ A) :
    Scheme.Modules.scalarsFromBase (p ≫ Spec.map f) =
      (Scheme.Modules.scalarsFromBase p).comp f.hom := by
  unfold Scheme.Modules.scalarsFromBase
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

section Coefficients

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {X T : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
  {L : LineBundle X} {n : ℕ} (s : Fin (n + 1) → GlobalSections L.obj)

/-- Evaluating coordinates after changing coefficients gives the same section ratios. -/
lemma chartRingHom_comp_mvMapGraded (g : T ⟶ X) (i : Fin (n + 1)) :
    (chartRingHom p s g i).comp (ProjSpace.mvMapGraded R A n).toRingHom =
      chartRingHom (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) s g i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change chartRingHom p s g i (MvPolynomial.map (algebraMap R A) (MvPolynomial.C r)) = _
    rw [MvPolynomial.map_C, chartRingHom_C, chartRingHom_C,
      ← Category.assoc, scalarsFromBase_specMap]
    rfl
  · intro j
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom,
      ProjSpace.mvMapGraded_X, chartRingHom_X]

/-- The actual affine linear-system chart map commutes with coefficient restriction. -/
lemma pointMap_comp_coefficientMap (g : T ⟶ X) (i : Fin (n + 1))
    (hg : ∀ t, g t ∈ trivializationOpen L.obj (s i)) :
    pointMap p s g i hg ≫ ProjSpace.map R A n =
      pointMap (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) s g i hg := by
  have hu : IsUnit (chartRingHom p s g i (ProjSpace.mvMapGraded R A n (MvPolynomial.X i))) := by
    rw [ProjSpace.mvMapGraded_X]
    exact isUnit_chartRingHom_X p s hg
  have h := chartMap_comp_projMap (projectiveSpaceGrading R n) (projectiveSpaceGrading A n)
    (ProjSpace.mvMapGraded R A n) (ProjSpace.irrelevant_le_map_mvMapGraded R A n)
    (chartRingHom p s g i) (projectiveSpace_X_mem R n i) one_pos hu
  unfold ProjectiveSpace projectiveSpaceGrading at h ⊢
  simp only [ProjSpace.mvMapGraded_X] at h
  refine h.trans ?_
  exact chartMap_ringHom_congr _ (chartRingHom_comp_mvMapGraded p s g i) _ _ _

/-- The glued linear-system morphism commutes with restriction of its coefficient ring. -/
lemma linearSystemMap_comp_coefficientMap
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap p hs ≫ ProjSpace.map R A n =
      linearSystemMap (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) hs := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := exists_mem_trivializationOpen hs x
  refine ⟨trivializationOpen L.obj (s i), hi, ?_⟩
  rw [← Category.assoc, comp_linearSystemMap p hs _ i (ι_mem _),
    pointMap_comp_coefficientMap,
    comp_linearSystemMap _ hs _ i (ι_mem _)]

end Coefficients

section IntegralComparison

variable {K : Type u} [CommRing K] {X S : Scheme.{u}} {L : LineBundle X} {n : ℕ}
  {s : Fin (n + 1) → GlobalSections L.obj}

/-- Passing from polynomial projective space to the integral model recovers the
integral linear-system morphism of the same actual sections. -/
lemma linearSystemMap_comp_polynomialToIntegral
    (p : X ⟶ Spec (CommRingCat.of K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    linearSystemMap p hs ≫ RelativeProjectiveSpace.polynomialToIntegral K n =
      integralLinearSystemMap hs := by
  let : Algebra (ULift.{u} ℤ) K :=
    ((Int.castRingHom K).comp ULift.ringEquiv.toRingHom).toAlgebra
  change linearSystemMap p hs ≫ ProjSpace.map (ULift.{u} ℤ) K n = _
  rw [linearSystemMap_comp_coefficientMap]
  unfold integralLinearSystemMap
  congr 1
  exact specULiftZIsTerminal.hom_ext _ _

/-- The polynomial projection of the relative linear-system map is its actual
linear-system map over the coefficient ring. -/
lemma relativeLinearSystemMap_toPolynomial (p : X ⟶ S)
    (a : S ⟶ Spec (CommRingCat.of K))
    (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i)) :
    relativeLinearSystemMap p hs ≫ RelativeProjectiveSpace.toPolynomial n a =
      linearSystemMap (p ≫ a) hs := by
  apply (cancel_mono (RelativeProjectiveSpace.affineComparisonIso K n).hom).mp
  simp only [RelativeProjectiveSpace.toPolynomial, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  apply RelativeProjectiveSpace.hom_ext
  · simp [linearSystemMap_toSpec]
  · simp only [Category.assoc, RelativeProjectiveSpace.map_toIntegral,
      relativeLinearSystemMap_toIntegral,
      RelativeProjectiveSpace.affineComparisonIso_hom_toIntegral]
    exact (linearSystemMap_comp_polynomialToIntegral (p ≫ a) hs).symm

/-- The integral linear system of the actual polynomial coordinate sections is
the canonical coefficient morphism to the integral model. -/
lemma integralLinearSystemMap_projectiveCoordinates (K : Type u) [CommRing K] (n : ℕ) :
    integralLinearSystemMap (projectiveCoordinates_generate K n) =
      RelativeProjectiveSpace.polynomialToIntegral K n := by
  rw [← linearSystemMap_comp_polynomialToIntegral (projectiveSpaceToSpec K n)
    (projectiveCoordinates_generate K n), linearSystemMap_projectiveCoordinates,
    Category.id_comp]

/-- The actual polynomial twist agrees with the twist pulled from the integral
model, with no model-comparison premise. -/
def polynomialIntegralTwistIso (K : Type u) [CommRing K] (n : ℕ) :
    (Scheme.Modules.pullback (RelativeProjectiveSpace.polynomialToIntegral K n)).obj
        (twistOne (ULift.{u} ℤ) n) ≅ twistOne K n :=
  (Scheme.Modules.pullbackCongr
      (integralLinearSystemMap_projectiveCoordinates K n).symm).app
      (twistOne (ULift.{u} ℤ) n) ≪≫
    linearSystemTwistIso (L := projectiveCoordinateLineBundle K n)
      (specULiftZIsTerminal.from (ProjectiveSpace K n))
      (twistOneCoordinate K n) (projectiveCoordinates_generate K n)

/-- The coefficient comparison preserves each actual homogeneous coordinate
section of the degree-one twist. -/
lemma polynomialIntegralTwistIso_coordinate (K : Type u) [CommRing K] (n : ℕ)
    (i : Fin (n + 1)) :
    (polynomialIntegralTwistIso K n).hom.app ⊤
        (pullbackSection (RelativeProjectiveSpace.polynomialToIntegral K n)
          (twistOne (ULift.{u} ℤ) n) (twistOneCoordinate (ULift.{u} ℤ) n i)) =
      twistOneCoordinate K n i := by
  change (linearSystemTwistIso (L := projectiveCoordinateLineBundle K n)
    (specULiftZIsTerminal.from (ProjectiveSpace K n)) (twistOneCoordinate K n)
    (projectiveCoordinates_generate K n)).hom.app ⊤
      (((Scheme.Modules.pullbackCongr
        (integralLinearSystemMap_projectiveCoordinates K n).symm).hom.app
          (twistOne (ULift.{u} ℤ) n)).app ⊤ _) = _
  rw [pullbackCongr_coordinate]
  exact linearSystemTwistIso_coordinate (L := projectiveCoordinateLineBundle K n)
    _ _ (projectiveCoordinates_generate K n) i

end IntegralComparison

end Langlands.AlgebraicGeometry.LinearSystem
