import Langlands.Geometry.FormalGroup.DeligneActionBaseChange

/-! # Natural group actions on the constructed Deligne Nilp functor -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory
open scoped MatrixGroups

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F]

/-- The identity corrected pair gives the identity natural automorphism. -/
@[simp]
theorem nilpSheafShiftReframeAut_one (hπ : algebraMap O F π ≠ 0) :
    nilpSheafShiftReframeAut (d := d) hπ 1 = 1 := by
  apply Aut.ext
  ext B q
  exact SheafDatum.IsoClass.shiftReframe_one hπ q

/-- The natural automorphisms retain the right-action order of frame precomposition. -/
theorem nilpSheafShiftReframeAut_mul (hπ : algebraMap O F π ≠ 0)
    (p r : shiftReframeSubgroup (d := d) hπ) :
    nilpSheafShiftReframeAut hπ (p * r) =
      nilpSheafShiftReframeAut hπ r * nilpSheafShiftReframeAut hπ p := by
  apply Aut.ext
  ext B q
  exact (SheafDatum.IsoClass.shiftReframe_mul hπ p r q).symm

/-- The corrected right action as a homomorphism to opposite natural automorphisms. -/
def nilpSheafShiftReframeHom (hπ : algebraMap O F π ≠ 0) :
    shiftReframeSubgroup (d := d) hπ →*
      (Aut (nilpSheafClassFunctor d π F hπ))ᵐᵒᵖ where
  toFun p := MulOpposite.op (nilpSheafShiftReframeAut hπ p)
  map_one' := by
    apply MulOpposite.unop_injective
    exact nilpSheafShiftReframeAut_one hπ
  map_mul' p r := by
    apply MulOpposite.unop_injective
    exact nilpSheafShiftReframeAut_mul hπ p r

/-- Evaluation of the corrected natural action is the existing class operation. -/
@[simp]
theorem nilpSheafShiftReframeHom_hom_app (hπ : algebraMap O F π ≠ 0)
    (p : shiftReframeSubgroup (d := d) hπ) (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F hπ B) :
    (nilpSheafShiftReframeHom hπ p).unop.asIso.hom.app B q =
      SheafDatum.IsoClass.shiftReframe hπ p q := rfl

section Valued

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- Compose the canonical determinant correction with the corrected natural right action. -/
def nilpSheafNormalizedReframeHom (hπ : Irreducible π) :
    ((Fin d → F) ≃ₗ[F] (Fin d → F)) →*
      (Aut (nilpSheafClassFunctor d π F
        (coefficientUniformizer_ne_zero (F := F) hπ)))ᵐᵒᵖ :=
  (nilpSheafShiftReframeHom _).comp (normalizedReframeHom hπ)

/-- The normalized homomorphism has the already constructed natural automorphism as value. -/
@[simp]
theorem nilpSheafNormalizedReframeHom_apply (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (nilpSheafNormalizedReframeHom hπ g).unop =
      nilpSheafNormalizedReframeAut hπ g := rfl

/-- Evaluation retains the actual determinant-normalized class operation. -/
@[simp]
theorem nilpSheafNormalizedReframeHom_hom_app (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafNormalizedReframeHom hπ g).unop.asIso.hom.app B q =
      SheafDatum.IsoClass.normalizedReframe hπ g q := rfl

/-- Every field scalar is the identity as a natural automorphism on Nilp. -/
@[simp]
theorem nilpSheafNormalizedReframeAut_scalar (hπ : Irreducible π) (a : Fˣ) :
    nilpSheafNormalizedReframeAut hπ (scalarReframeHom d F a) = 1 := by
  apply Aut.ext
  ext B q
  exact SheafDatum.IsoClass.normalizedReframe_scalar hπ a q

/-- The normalized natural homomorphism kills every scalar frame change. -/
@[simp]
theorem nilpSheafNormalizedReframeHom_scalar (hπ : Irreducible π) (a : Fˣ) :
    nilpSheafNormalizedReframeHom hπ (scalarReframeHom d F a) = 1 := by
  apply MulOpposite.unop_injective
  exact nilpSheafNormalizedReframeAut_scalar hπ a

/-- An actual projective matrix representative has its normalized natural GL action. -/
@[simp]
theorem nilpSheafProjectiveReframeAut_mk (hπ : Irreducible π) (g : GL (Fin d) F) :
    nilpSheafProjectiveReframeAut hπ (Matrix.ProjGenLinGroup.mk g) =
      nilpSheafNormalizedReframeAut hπ (matrixReframeEquiv d F g) := by
  apply Aut.ext
  ext B q
  exact SheafDatum.IsoClass.projectiveReframe_mk hπ g q

/-- The actual projective identity gives the identity natural automorphism. -/
@[simp]
theorem nilpSheafProjectiveReframeAut_one (hπ : Irreducible π) :
    nilpSheafProjectiveReframeAut (d := d) (F := F) hπ 1 = 1 := by
  apply Aut.ext
  ext B q
  exact SheafDatum.IsoClass.projectiveReframe_one hπ q

/-- Actual projective multiplication has the same right-action order on the functor. -/
theorem nilpSheafProjectiveReframeAut_mul (hπ : Irreducible π) (g h : PGL(d, F)) :
    nilpSheafProjectiveReframeAut hπ (g * h) =
      nilpSheafProjectiveReframeAut hπ h * nilpSheafProjectiveReframeAut hπ g := by
  apply Aut.ext
  ext B q
  exact (SheafDatum.IsoClass.projectiveReframe_mul hπ g h q).symm

/-- The actual PGL right action as a homomorphism to opposite natural automorphisms. -/
def nilpSheafProjectiveReframeHom (hπ : Irreducible π) :
    PGL(d, F) →* (Aut (nilpSheafClassFunctor d π F
      (coefficientUniformizer_ne_zero (F := F) hπ)))ᵐᵒᵖ where
  toFun g := MulOpposite.op (nilpSheafProjectiveReframeAut hπ g)
  map_one' := by
    apply MulOpposite.unop_injective
    exact nilpSheafProjectiveReframeAut_one hπ
  map_mul' g h := by
    apply MulOpposite.unop_injective
    exact nilpSheafProjectiveReframeAut_mul hπ g h

/-- The projective homomorphism evaluates to the existing actual projective class operation. -/
@[simp]
theorem nilpSheafProjectiveReframeHom_hom_app (hπ : Irreducible π) (g : PGL(d, F))
    (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafProjectiveReframeHom hπ g).unop.asIso.hom.app B q =
      SheafDatum.IsoClass.projectiveReframe hπ g q := rfl

/-- The natural projective action recovers the normalized GL homomorphism on representatives. -/
@[simp]
theorem nilpSheafProjectiveReframeHom_mk (hπ : Irreducible π) (g : GL (Fin d) F) :
    nilpSheafProjectiveReframeHom hπ (Matrix.ProjGenLinGroup.mk g) =
      nilpSheafNormalizedReframeHom hπ (matrixReframeEquiv d F g) := by
  apply MulOpposite.unop_injective
  exact nilpSheafProjectiveReframeAut_mk hπ g

/-- The natural action of every actual scalar matrix is trivial. -/
@[simp]
theorem nilpSheafNormalizedReframeHom_scalarMatrix (hπ : Irreducible π) (a : Fˣ) :
    nilpSheafNormalizedReframeHom hπ
      (matrixReframeEquiv d F (Matrix.GeneralLinearGroup.scalar (Fin d) a)) = 1 := by
  rw [matrixReframeEquiv_scalar, nilpSheafNormalizedReframeHom_scalar]

/-- The associated ordinary left PGL action uses inverse frame precomposition. -/
def nilpSheafProjectiveLeftHom (hπ : Irreducible π) :
    PGL(d, F) →* Aut (nilpSheafClassFunctor d π F
      (coefficientUniformizer_ne_zero (F := F) hπ)) where
  toFun g := nilpSheafProjectiveReframeAut hπ g⁻¹
  map_one' := by
    rw [inv_one, nilpSheafProjectiveReframeAut_one]
  map_mul' g h := by
    rw [mul_inv_rev, nilpSheafProjectiveReframeAut_mul]

/-- The ordinary left natural action evaluates to the inverse projective operation. -/
@[simp]
theorem nilpSheafProjectiveLeftHom_hom_app (hπ : Irreducible π) (g : PGL(d, F))
    (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafProjectiveLeftHom hπ g).asIso.hom.app B q =
      SheafDatum.IsoClass.projectiveReframe hπ g⁻¹ q := rfl

/-- A matrix class acts in the ordinary left convention by its inverse normalized frame change. -/
theorem nilpSheafProjectiveLeftHom_mk_hom_app (hπ : Irreducible π) (g : GL (Fin d) F)
    (B : FormalGroup.Nilp.{u, u} O π)
    (q : NilpSheafIsoClass d π F (coefficientUniformizer_ne_zero (F := F) hπ) B) :
    (nilpSheafProjectiveLeftHom hπ (Matrix.ProjGenLinGroup.mk g)).asIso.hom.app B q =
      SheafDatum.IsoClass.normalizedReframe hπ (matrixReframeEquiv d F g⁻¹) q := by
  rw [nilpSheafProjectiveLeftHom_hom_app, ← map_inv,
    SheafDatum.IsoClass.projectiveReframe_mk]

end Valued

end Langlands.DeligneFormalSpace
