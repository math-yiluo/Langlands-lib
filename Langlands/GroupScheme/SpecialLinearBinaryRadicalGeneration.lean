import Langlands.GroupScheme.SpecialLinearBinaryBigCell
import Langlands.GroupScheme.SpecialLinearBinaryUpperParabolic
import Langlands.GroupScheme.SpecialLinearBinaryUpperRadical
import Langlands.GroupScheme.Rational.ElementarySubgroup

/-! # Rational parabolic radicals generate the binary special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

section Weyl

variable (k : Type u) [CommRing k]

/-- Conjugation by the explicit Weyl matrix takes the upper root to the lower root. -/
theorem weylMatrix_conjugate_upper (a : k) :
    BinaryUpper.weylMatrix (A := k) * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) a * (BinaryUpper.weylMatrix (A := k))⁻¹ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (-a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change !![0, -1; 1, 0] * Matrix.transvection (0 : Fin 2) 1 a =
    Matrix.transvection (1 : Fin 2) 0 (-a) * !![0, -1; 1, 0]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply]

/-- The actual rational point corresponding to the explicit Weyl matrix. -/
def weylPoint :
    rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) :=
  (rationalMatrixEquiv k).symm (BinaryUpper.weylMatrix (A := k))

@[simp] theorem rationalMatrixEquiv_weylPoint :
    rationalMatrixEquiv k (weylPoint k) = BinaryUpper.weylMatrix (A := k) :=
  (rationalMatrixEquiv k).apply_symm_apply _

end Weyl

section NormalGeneration

variable (k : Type u) [Field k]
variable (N : Subgroup
  (rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)))) [N.Normal]

/-- A normal subgroup containing the actual upper root image contains the lower root image. -/
theorem lower_range_le_of_normal_upper_range
    (hupper : (rationalPoints.map (upperMap (CommRingCat.of k))).range ≤ N) :
    (rationalPoints.map (lowerMap (CommRingCat.of k))).range ≤ N := by
  rintro _ ⟨x, rfl⟩
  let a := (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((VectorGroup.coordinates (CommRingCat.of k) 1 _ x).toAdd 0)
  obtain ⟨y, hy⟩ := exists_rational_rootPoint k (show (0 : Fin 2) ≠ 1 by decide) (-a)
  have hx : rationalMatrixEquiv k
      (rationalPoints.map (lowerMap (CommRingCat.of k)) x) =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) a :=
    rationalMatrixEquiv_rootMap k _ x
  have heq : weylPoint k * rationalPoints.map (upperMap (CommRingCat.of k)) y *
      (weylPoint k)⁻¹ = rationalPoints.map (lowerMap (CommRingCat.of k)) x := by
    apply (rationalMatrixEquiv k).injective
    rw [map_mul, map_mul, map_inv, rationalMatrixEquiv_weylPoint, hy, hx,
      weylMatrix_conjugate_upper, neg_neg]
  rw [← heq]
  exact (inferInstance : N.Normal).conj_mem _ (hupper ⟨y, rfl⟩) _

/-- The actual upper additive root normally generates every rational point of split SL₂. -/
theorem eq_top_of_normal_upper_image
    (hupper : (rationalPoints.map (upperMap (CommRingCat.of k))).range ≤ N) : N = ⊤ :=
  eq_top_of_root_images k N hupper (lower_range_le_of_normal_upper_range k N hupper)

end NormalGeneration

section ParabolicGeneration

variable (k : Type u) [Field k]

/-- Actual rational parabolic radicals generate every rational point of split SL₂. -/
theorem parabolicElementarySubgroup_eq_top :
    parabolicElementarySubgroup (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) = ⊤ := by
  apply eq_top_of_normal_upper_image
  have h := parabolic_radical_range_le_elementarySubgroup
    (BinaryUpper.isParabolicSubgroup_inclusion k)
    (BinaryUpper.isGeometricUnipotentRadical_upperRootMap (k := k))
  rwa [BinaryUpper.upperRootMap_comp_inclusion] at h

/-- Any subgroup containing all actual rational parabolic radical images is the whole SL₂
point group; this consequence does not require a separate normality premise. -/
theorem eq_top_of_parabolic_radical_images
    (N : Subgroup (rationalPoints (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k))))
    (hN : ∀ (P U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) : N = ⊤ := by
  apply top_unique
  rw [← parabolicElementarySubgroup_eq_top k]
  exact (parabolicElementarySubgroup_le_iff N).mpr hN

end ParabolicGeneration

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
