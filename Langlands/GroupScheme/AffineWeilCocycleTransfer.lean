import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.AlgebraicGeometry.PointTopology.WeilRestrictionRepresentabilityProof
import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.CocycleRelativeTrivialization

/-! # Transfer of natural cocycles from an affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineWeil

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (H : GroupScheme (Spec (CommRingCat.of B))) [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local notation "b" => Spec.algebraMap A B
local notation "P" => Over.pullback (Spec.algebraMap A B)
local notation "W" => groupScheme A B H
local notation "eval" => affineWeilRestrictionCounit A B H.X
local notation "compare" => affineWeilRestrictionComparison A B H.X

local instance : GrpObj (affineWeilRestriction A B H.X) := (W).grp

private theorem comparison_mul_spectrum (C : Type u) [CommRing C] [Algebra A C]
    (x y : ringTest A C ⟶ (W).X) : compare (ringTest A C) (x * y) =
      compare (ringTest A C) x * compare (ringTest A C) y := by
  have h (z : ringTest A C ⟶ (W).X) : compare (ringTest A C) z =
      (ringBaseChangeSpectrumIso A B C).hom ≫ pointsEquiv A B H C z := by
    rw [affineWeilRestrictionComparison_affine]
    exact congrArg (fun q => (ringBaseChangeSpectrumIso A B C).hom ≫ q z)
      (pointsEquiv_eq A B H C).symm
  rw [h, h, h, map_mul, MonObj.comp_mul]

private theorem comparison_mul_of_isAffine (T : Over (Spec (CommRingCat.of A))) [IsAffine T.left]
    (x y : T ⟶ (W).X) : compare T (x * y) = compare T x * compare T y := by
  let e := affineSchemeOverIso A T
  apply (cancel_epi ((P).map e.inv)).mp
  rw [MonObj.comp_mul, ← affineWeilRestrictionComparison_natural,
    ← affineWeilRestrictionComparison_natural, ← affineWeilRestrictionComparison_natural,
    MonObj.comp_mul]
  exact comparison_mul_spectrum A B H _ _ _

private theorem comparison_mul (T : Over (Spec (CommRingCat.of A))) (x y : T ⟶ (W).X) :
    compare T (x * y) = compare T x * compare T y := by
  let Z := (W).X ⊗ (W).X
  let : IsAffine Z.left := inferInstanceAs (IsAffine (pullback (W).X.hom (W).X.hom))
  let p : Z ⟶ (W).X := fst _ _
  let q : Z ⟶ (W).X := snd _ _
  let t : T ⟶ Z := lift x y
  have hx : t ≫ p = x := lift_fst _ _
  have hy : t ≫ q = y := lift_snd _ _
  have hxy : t ≫ (p * q) = x * y := by rw [MonObj.comp_mul, hx, hy]
  rw [← hxy, affineWeilRestrictionComparison_natural,
    comparison_mul_of_isAffine A B H Z p q, MonObj.comp_mul,
    ← affineWeilRestrictionComparison_natural, ← affineWeilRestrictionComparison_natural, hx, hy]

private theorem comparison_one (T : Over (Spec (CommRingCat.of A))) :
    compare T (1 : T ⟶ (W).X) = 1 := by
  have h := comparison_mul A B H T 1 1
  rw [one_mul] at h
  exact (mul_left_cancel (show compare T 1 * 1 = compare T 1 * compare T 1 by
    rw [mul_one]; exact h)).symm

private theorem pullback_evaluation_postcomp
    (T : Over (Spec (CommRingCat.of B))) (x : T ⟶ ((GroupScheme.baseChange (b)).obj W).X) :
    ((Over.mapPullbackAdj (b)).unit.app T) ≫
        compare ((Over.map (b)).obj T) (baseChangePointsEquiv (b) W T x) = x ≫ (eval) := by
  change ((Over.mapPullbackAdj (b)).unit.app T) ≫ (P).map (baseChangePointsEquiv (b) W T x) ≫ (eval) = _
  have h : (Over.mapPullbackAdj (b)).unit.app T ≫ (P).map (baseChangePointsEquiv (b) W T x) = x := by
    change (baseChangePointsEquiv (b) W T).symm (baseChangePointsEquiv (b) W T x) = x
    exact (baseChangePointsEquiv (b) W T).symm_apply_apply x
  rw [← Category.assoc, h]

private def evaluationOnPoints (T : Over (Spec (CommRingCat.of B))) :
    (T ⟶ ((GroupScheme.baseChange (b)).obj W).X) →* (T ⟶ H.X) where
  toFun x := x ≫ (eval)
  map_one' := by
    rw [← pullback_evaluation_postcomp A B H, map_one, comparison_one A B H, MonObj.comp_one]
  map_mul' x y := by
    rw [← pullback_evaluation_postcomp A B H, ← pullback_evaluation_postcomp A B H T x,
      ← pullback_evaluation_postcomp A B H T y, map_mul, comparison_mul A B H, MonObj.comp_mul]

private theorem evaluationOnPoints_natural {T T' : Over (Spec (CommRingCat.of B))}
    (a : T' ⟶ T) (x : T ⟶ ((GroupScheme.baseChange (b)).obj W).X) :
    evaluationOnPoints A B H T' (a ≫ x) = a ≫ evaluationOnPoints A B H T x :=
  Category.assoc a x (eval)

/-- The canonical Weil-restriction comparison morphism is a group homomorphism. -/
def cocycleEvaluation : (GroupScheme.baseChange (b)).obj W ⟶ H :=
  homOfPoints (evaluationOnPoints A B H) (evaluationOnPoints_natural A B H)

private theorem cocycleEvaluation_hom : (cocycleEvaluation A B H).hom.hom = (eval) := by
  have h := comp_homOfPoints (evaluationOnPoints A B H)
    (evaluationOnPoints_natural A B H) ((GroupScheme.baseChange (b)).obj W).X (𝟙 _)
  change 𝟙 _ ≫ (cocycleEvaluation A B H).hom.hom = 𝟙 _ ≫ (eval) at h
  exact (Category.id_comp _).symm.trans (h.trans (Category.id_comp _))

variable {U : Over (Spec (CommRingCat.of A))}

/-- Transfer a natural cocycle using the actual evaluation on the base-changed cover. -/
def transferCocycle (ξ : Cocycle W U) : Cocycle H ((P).obj U) :=
  (ξ.baseChange (b) ((P).obj U) ((Over.mapPullbackAdj (b)).counit.app U)).map
    (cocycleEvaluation A B H)

theorem transferCocycle_value_pullback (ξ : Cocycle W U)
    {Z : Over (Spec (CommRingCat.of A))} (a c : Z ⟶ U) :
    (transferCocycle A B H ξ).toFun ((P).map a) ((P).map c) = compare Z (ξ.toFun a c) := by
  let r := (Over.mapPullbackAdj (b)).counit
  change (ξ.baseChange (b) _ (r.app U)).toFun ((P).map a) ((P).map c) ≫
      (cocycleEvaluation A B H).hom.hom = (P).map (ξ.toFun a c) ≫ (eval)
  rw [cocycleEvaluation_hom]
  congr 1
  apply (baseChangePointsEquiv (b) W ((P).obj Z)).injective
  rw [Cocycle.baseChange_toFun]
  have ha : (Over.map (b)).map ((P).map a) ≫ r.app U = r.app Z ≫ a := r.naturality a
  have hc : (Over.map (b)).map ((P).map c) ≫ r.app U = r.app Z ≫ c := r.naturality c
  rw [ha, hc, ξ.naturality]
  exact (r.naturality (ξ.toFun a c)).symm

/-- Triviality of the transfer reflects triviality on the original affine cover. -/
theorem isTrivial_of_transferCocycle (ξ : Cocycle W U) [IsAffine U.left]
    (h : (transferCocycle A B H ξ).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨g, hg⟩ := (affineWeilRestrictionComparison_bijective_of_isAffine A B H.X U).surjective f
  let Z := U ⊗ U
  let : IsAffine Z.left := inferInstanceAs (IsAffine (pullback U.hom U.hom))
  refine ⟨g, fun a c => ?_⟩
  apply Cocycle.toFun_eq_of_universal_eq ξ (Cocycle.coboundary g)
  apply (affineWeilRestrictionComparison_bijective_of_isAffine A B H.X Z).injective
  rw [← transferCocycle_value_pullback, hf]
  change _ = compare Z (((fst U U) ≫ g) * (((snd U U) ≫ g)⁻¹))
  have hi (x : Z ⟶ (W).X) : compare Z x⁻¹ = (compare Z x)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← comparison_mul A B H, mul_inv_cancel, comparison_one A B H]
  rw [comparison_mul A B H, hi, affineWeilRestrictionComparison_natural,
    affineWeilRestrictionComparison_natural, hg]

end Langlands.GroupScheme.AffineWeil
