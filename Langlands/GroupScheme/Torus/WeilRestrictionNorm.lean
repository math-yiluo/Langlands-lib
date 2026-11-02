import Langlands.Algebra.TensorNorm
import Langlands.GroupScheme.Torus.WeilRestrictionCommutative

/-! # Scalar and norm morphisms of the Weil-restricted multiplicative group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]

/-- Scalar units enter the right tensor factor. -/
def scalarUnits (R : Type u) [CommRing R] [Algebra A R] :
    Rˣ →* (B ⊗[A] R)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toMonoidHom

/-- Scalar units commute with every change of test algebra. -/
theorem scalarUnits_naturality {R R' : Type u} [CommRing R] [Algebra A R]
    [CommRing R'] [Algebra A R'] (g : R →ₐ[A] R') (x : Rˣ) :
    scalarUnits A B R' (Units.map g.toMonoidHom x) =
      Units.map (Algebra.TensorProduct.lTensor (S := B) B g).toMonoidHom
        (scalarUnits A B R x) := by
  apply Units.ext
  simp [scalarUnits, Algebra.TensorProduct.includeRight_apply]

section Scalar

variable [Module.Finite A B] [Module.Projective A B]

/-- The scalar map on points of an arbitrary test scheme. -/
def scalarPoints (T : Over (Spec A)) :
    (T ⟶ (Gm (Spec A)).X) →* (T ⟶ (groupScheme A B).X) :=
  (pointsEquiv A B T).symm.toMonoidHom.comp
    ((scalarUnits A B ((algΓ A).obj T).unop).comp (Gm.pointsEquiv (Spec A) T).toMonoidHom)

@[simp] theorem pointsEquiv_scalarPoints (T : Over (Spec A))
    (x : T ⟶ (Gm (Spec A)).X) :
    pointsEquiv A B T (scalarPoints A B T x) =
      scalarUnits A B ((algΓ A).obj T).unop (Gm.pointsEquiv (Spec A) T x) :=
  (pointsEquiv A B T).apply_symm_apply _

theorem scalarPoints_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec A)).X) :
    scalarPoints A B T' (a ≫ x) = a ≫ scalarPoints A B T x := by
  apply (pointsEquiv A B T').injective
  rw [pointsEquiv_scalarPoints, pointsEquiv_naturality, pointsEquiv_scalarPoints,
    Gm.pointsEquiv_naturality]
  exact scalarUnits_naturality A B ((algΓ A).map a).unop.hom _

/-- The actual scalar homomorphism `G_m → Res_{B/A} G_m`. -/
def scalar : (Gm (Spec A)).toGrp ⟶ groupScheme A B :=
  homOfPoints (scalarPoints A B) (scalarPoints_naturality A B)

/-- On all tests, the scalar homomorphism is the unit map of `r ↦ 1 ⊗ r`. -/
theorem scalar_points (T : Over (Spec A)) (x : T ⟶ (Gm (Spec A)).X) :
    pointsEquiv A B T (x ≫ (scalar A B).hom.hom) =
      scalarUnits A B ((algΓ A).obj T).unop (Gm.pointsEquiv (Spec A) T x) := by
  rw [scalar, comp_homOfPoints, pointsEquiv_scalarPoints]

/-- The scalar homomorphism in the commutative group-scheme category. -/
def scalarHom : Gm (Spec A) ⟶ commGroupScheme A B :=
  Additive.ofMul (scalar A B)

end Scalar

section Norm

variable [Module.Finite A B] [Module.Free A B]

/-- The determinant norm on points of an arbitrary test scheme. -/
def normPoints (T : Over (Spec A)) :
    (T ⟶ (groupScheme A B).X) →* (T ⟶ (Gm (Spec A)).X) :=
  (Gm.pointsEquiv (Spec A) T).symm.toMonoidHom.comp
    ((Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop).comp
      (pointsEquiv A B T).toMonoidHom)

@[simp] theorem pointsEquiv_normPoints (T : Over (Spec A))
    (x : T ⟶ (groupScheme A B).X) :
    Gm.pointsEquiv (Spec A) T (normPoints A B T x) =
      Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop (pointsEquiv A B T x) :=
  (Gm.pointsEquiv (Spec A) T).apply_symm_apply _

theorem normPoints_naturality {T T' : Over (Spec A)} (a : T' ⟶ T)
    (x : T ⟶ (groupScheme A B).X) :
    normPoints A B T' (a ≫ x) = a ≫ normPoints A B T x := by
  apply (Gm.pointsEquiv (Spec A) T').injective
  rw [pointsEquiv_normPoints, Gm.pointsEquiv_naturality, pointsEquiv_normPoints,
    pointsEquiv_naturality]
  exact Langlands.Algebra.tensorNormUnits_naturality ((algΓ A).map a).unop.hom _

/-- The actual norm homomorphism `Res_{B/A} G_m → G_m` for finite free `B/A`. -/
def norm : groupScheme A B ⟶ (Gm (Spec A)).toGrp :=
  homOfPoints (normPoints A B) (normPoints_naturality A B)

/-- On all tests, the norm homomorphism is the determinant norm of the tensor algebra. -/
theorem norm_points (T : Over (Spec A)) (x : T ⟶ (groupScheme A B).X) :
    Gm.pointsEquiv (Spec A) T (x ≫ (norm A B).hom.hom) =
      Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop (pointsEquiv A B T x) := by
  rw [norm, comp_homOfPoints, pointsEquiv_normPoints]

/-- The norm homomorphism in the commutative group-scheme category. -/
def normHom : commGroupScheme A B ⟶ Gm (Spec A) :=
  Additive.ofMul (norm A B)

/-- Scalar followed by norm is the rank power map on every test scheme. -/
theorem scalar_norm_points (T : Over (Spec A)) (x : T ⟶ (Gm (Spec A)).X) :
    Gm.pointsEquiv (Spec A) T (x ≫ (scalar A B ≫ norm A B).hom.hom) =
      Gm.pointsEquiv (Spec A) T x ^ Module.finrank A B := by
  rw [Grp.comp_hom_hom, ← Category.assoc, norm_points, scalar_points]
  exact Langlands.Algebra.tensorNormUnits_scalar _

/-- As actual morphisms, scalar followed by norm is multiplication by the rank. -/
theorem scalarHom_comp_normHom :
    scalarHom A B ≫ normHom A B =
      (Module.finrank A B : ℤ) • 𝟙 (Gm (Spec A)) := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  apply (Gm.pointsEquiv (Spec A) T).injective
  change Gm.pointsEquiv (Spec A) T (x ≫ (scalar A B ≫ norm A B).hom.hom) = _
  rw [scalar_norm_points, Gm.comp_zsmul_id, map_zpow, zpow_natCast]

end Norm

end Langlands.GroupScheme.WeilGm
