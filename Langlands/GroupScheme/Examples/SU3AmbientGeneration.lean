import Langlands.GroupScheme.Examples.SU3DynamicRoots
import Langlands.GroupScheme.Examples.SU3RationalPoints
import Langlands.GroupScheme.Rational.DynamicElementarySubgroup

/-! # Full actual SU3 images in the parabolic elementary subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SU3Root

section Coefficients

variable {A B : Type u} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

/-- Coefficient equivalence takes the original upper matrix to the upper matrix
with its two coordinates transported. -/
theorem specialUnitaryRingEquiv_upper (e : A ≃+* B)
    (he : ∀ a, e (c.bar a) = d.bar (e a)) (x : Parameters c) :
    specialUnitaryRingEquiv e he (upperSpecialUnitaryHom c x) =
      upperSpecialUnitaryHom d (Parameters.mapEquiv e he x) := by
  apply Subtype.ext
  apply Units.ext
  rw [specialUnitaryRingEquiv_val]
  exact congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) B =>
    (g : Matrix (Fin 3) (Fin 3) B)) (Parameters.embedding_map e.toRingHom he x).symm

end Coefficients

namespace SchemeModel

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]

/-- Evaluating the tensor coefficients identifies the actual upper test points
with the original rational upper matrices. -/
theorem rationalCoeffEquiv_rationalUpper
    (x : Parameters (coefficientInvolution k L (baseAffineTest k))) :
    GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L)
        (rationalUpper k L (Parameters.mapEquiv
          (rationalCoefficientEquiv k L).toRingEquiv
          (rationalCoefficientEquiv_bar k L) x)) =
      upperPoints k L (baseAffineTest k) x := by
  apply (pointsEquiv k L (baseAffineTest k)).injective
  apply (specialUnitaryRingEquiv (rationalCoefficientEquiv k L).toRingEquiv
    (rationalCoefficientEquiv_bar k L)).injective
  change rationalMatrixEquiv k L (rationalUpper k L _) = _
  rw [pointsEquiv_upperPoints, specialUnitaryRingEquiv_upper]
  exact (rationalMatrixEquiv k L).apply_symm_apply _

/-- The original rational upper matrices belong to the actual all-test upper
subgroup at the identity test. -/
theorem rationalUpper_mem_upperFunctor (x : Parameters (fieldInvolution k L)) :
    rationalUpper k L x ∈ (upperFunctor k L).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨y, rfl⟩ := (Parameters.mapEquiv
    (rationalCoefficientEquiv k L).toRingEquiv
    (rationalCoefficientEquiv_bar k L)).surjective x
  have hb : GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L)
      (rationalUpper k L (Parameters.mapEquiv
        (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L) y)) ∈
      (upperFunctor k L).carrier (baseAffineTest k) := by
    rw [rationalCoeffEquiv_rationalUpper]
    exact ⟨y, rfl⟩
  have h := (upperFunctor k L).comp_mem
    (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv hb
  have heq : (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv ≫
      GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L)
        (rationalUpper k L (Parameters.mapEquiv
          (rationalCoefficientEquiv k L).toRingEquiv
          (rationalCoefficientEquiv_bar k L) y)) =
      rationalUpper k L (Parameters.mapEquiv
        (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L) y) := by
    change (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).inv ≫
      ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ _) = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rwa [heq] at h

/-- Every original rational upper matrix contracts to the identity under the
actual diagonal cocharacter. -/
theorem rationalUpper_range_le_dynamicUnipotent :
    (rationalUpper k L).range ≤
      (Dynamic.unipotent (cocharacter k L)).carrier (Over.mk (𝟙 _)) := by
  rintro _ ⟨x, rfl⟩
  exact upperFunctor_le_dynamicUnipotent k L _ (rationalUpper_mem_upperFunctor k L x)

/-- The actual rational point represented by the determinant-one Weyl matrix. -/
def weylPoint : rationalPoints (groupScheme k L) :=
  (rationalMatrixEquiv k L).symm
    ⟨weylElement, weylElement_mem_specialUnitarySubgroup (fieldInvolution k L)⟩

@[simp] theorem rationalMatrixEquiv_weylPoint :
    (rationalMatrixEquiv k L (weylPoint k L)).1 = weylElement := by
  exact congrArg Subtype.val ((rationalMatrixEquiv k L).apply_symm_apply _)

/-- Weyl conjugation takes the original actual upper rational point to the
original opposite rational point, with the same parameter. -/
theorem weylPoint_conjugate_rationalUpper (x : Parameters (fieldInvolution k L)) :
    weylPoint k L * rationalUpper k L x * (weylPoint k L)⁻¹ =
      rationalLower k L x := by
  apply (rationalMatrixEquiv k L).injective
  apply Subtype.ext
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    rationalMatrixEquiv_weylPoint, rationalMatrixEquiv_upper, rationalMatrixEquiv_lower]
  rfl

/-- A normal subgroup containing the actual upper rational family contains the
actual opposite rational family. -/
theorem lower_range_le_of_normal_upper_range
    (N : Subgroup (rationalPoints (groupScheme k L))) [N.Normal]
    (hu : (rationalUpper k L).range ≤ N) :
    (rationalLower k L).range ≤ N := by
  rintro _ ⟨x, rfl⟩
  rw [← weylPoint_conjugate_rationalUpper]
  exact (inferInstance : N.Normal).conj_mem _ (hu ⟨x, rfl⟩) _

/-- The original upper rational family normally generates the entire actual
rational-point group. -/
theorem eq_top_of_normal_upper_range
    (N : Subgroup (rationalPoints (groupScheme k L))) [N.Normal]
    (hu : (rationalUpper k L).range ≤ N) : N = ⊤ :=
  eq_top_of_rational_roots k L N hu (lower_range_le_of_normal_upper_range k L N hu)

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A normal target subgroup containing the composed upper dynamic subgroup
contains the whole image of the actual SU3 rational-point group. -/
theorem rationalPoints_range_le_of_upper_dynamic
    (f : groupScheme k L ⟶ G) (N : Subgroup (rationalPoints G)) [N.Normal]
    (hu : (Dynamic.unipotent (cocharacter k L ≫ f)).carrier (Over.mk (𝟙 _)) ≤ N) :
    (rationalPoints.map f).range ≤ N := by
  have htop : N.comap (rationalPoints.map f) = ⊤ := by
    apply eq_top_of_normal_upper_range k L
    rintro _ ⟨x, rfl⟩
    exact hu (Dynamic.unipotent_le_comap (cocharacter k L) f _
      (rationalUpper_range_le_dynamicUnipotent k L ⟨x, rfl⟩))
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ N.comap (rationalPoints.map f) := by
    rw [htop]
    trivial
  exact hx

/-- The full actual SU3 rational image lies in the target's actual parabolic
elementary subgroup over every separable quadratic field extension. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G) (f : groupScheme k L ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_upper_dynamic k L f (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG (cocharacter k L ≫ f))

end SchemeModel
end Langlands.GroupScheme.SU3Root
