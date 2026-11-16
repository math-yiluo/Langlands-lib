import Langlands.Geometry.FormalGroup.DeligneScalarClass
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-! # The actual projective linear action on Deligne isomorphism classes -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry
open scoped MatrixGroups

/-- The standard-basis equivalence from actual invertible matrices to frame automorphisms. -/
def matrixReframeEquiv (d : ℕ) (F : Type u) [Field F] :
    GL (Fin d) F ≃* ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d → F))

/-- An actual scalar matrix gives the actual scalar frame automorphism. -/
@[simp]
theorem matrixReframeEquiv_scalar {d : ℕ} {F : Type u} [Field F] (a : Fˣ) :
    matrixReframeEquiv d F (Matrix.GeneralLinearGroup.scalar (Fin d) a) =
      scalarReframeHom d F a := by
  apply LinearEquiv.ext
  intro v
  change Matrix.mulVec (Matrix.scalar (Fin d) (a : F)) v = (a : F) • v
  funext i
  simp [Matrix.scalar, Matrix.mulVec_diagonal]

variable {O F : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field F] [Algebra O F] [IsFractionRing O F]
  {d : ℕ} [NeZero d] {π : O} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafDatum.IsoClass

variable (hπ : Irreducible π)

/-- The actual normalized right action as a homomorphism to opposite permutations. -/
def normalizedReframePermHom :
    ((Fin d → F) ≃ₗ[F] (Fin d → F)) →*
      (Equiv.Perm (IsoClass (d := d) (π := π) (φ := φ)
        (coefficientUniformizer_ne_zero (F := F) hπ)))ᵐᵒᵖ where
  toFun g := MulOpposite.op (normalizedReframeEquiv hπ g)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Equiv.ext
    intro q
    exact normalizedReframe_one hπ q
  map_mul' g h := by
    apply MulOpposite.unop_injective
    apply Equiv.ext
    intro q
    exact (normalizedReframe_mul hπ g h q).symm

/-- Descend the constructed action through Mathlib's actual matrix projective quotient. -/
def projectiveReframeHom :
    PGL(d, F) →*
      (Equiv.Perm (IsoClass (d := d) (π := π) (φ := φ)
        (coefficientUniformizer_ne_zero (F := F) hπ)))ᵐᵒᵖ :=
  Matrix.ProjGenLinGroup.lift
    ((normalizedReframePermHom hπ).comp (matrixReframeEquiv d F).toMonoidHom) (by
      apply MonoidHom.ext
      intro a
      apply MulOpposite.unop_injective
      apply Equiv.ext
      intro q
      change normalizedReframe hπ
        (matrixReframeEquiv d F (Matrix.GeneralLinearGroup.scalar (Fin d) a)) q = q
      rw [matrixReframeEquiv_scalar]
      exact normalizedReframe_scalar hπ a q)

/-- Apply an actual projective element to the genuine admissible classes on the right. -/
def projectiveReframe (g : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ) :=
  (projectiveReframeHom hπ g).unop q

/-- Representatives act by the already constructed normalized general linear operation. -/
@[simp]
theorem projectiveReframe_mk (g : GL (Fin d) F)
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    projectiveReframe hπ (Matrix.ProjGenLinGroup.mk g) q =
      normalizedReframe hπ (matrixReframeEquiv d F g) q := rfl

@[simp]
theorem projectiveReframe_one
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    projectiveReframe hπ 1 q = q := by
  simp [projectiveReframe]

/-- The projective operation satisfies the same right-action product law. -/
theorem projectiveReframe_mul (g h : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    projectiveReframe hπ h (projectiveReframe hπ g q) =
      projectiveReframe hπ (g * h) q := by
  simp only [projectiveReframe, map_mul, MulOpposite.unop_mul]
  rfl

@[simp]
theorem projectiveReframe_inv_projectiveReframe (g : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    projectiveReframe hπ g⁻¹ (projectiveReframe hπ g q) = q := by
  rw [projectiveReframe_mul, mul_inv_cancel, projectiveReframe_one]

@[simp]
theorem projectiveReframe_projectiveReframe_inv (g : PGL(d, F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    projectiveReframe hπ g (projectiveReframe hπ g⁻¹ q) = q := by
  rw [projectiveReframe_mul, inv_mul_cancel, projectiveReframe_one]

/-- The descended projective operation is an actual permutation of the existing classes. -/
def projectiveReframeEquiv (g : PGL(d, F)) :
    Equiv.Perm (IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :=
  (projectiveReframeHom hπ g).unop

/-- The frame-precomposition convention is a left action of the opposite projective group. -/
@[instance_reducible]
def projectiveReframeRightAction :
    MulAction (PGL(d, F))ᵐᵒᵖ
      (IsoClass (d := d) (π := π) (φ := φ)
        (coefficientUniformizer_ne_zero (F := F) hπ)) where
  smul g q := projectiveReframe hπ g.unop q
  one_smul := projectiveReframe_one hπ
  mul_smul g h q := (projectiveReframe_mul hπ h.unop g.unop q).symm

/-- The associated ordinary left projective action uses the inverse frame precomposition. -/
@[instance_reducible]
def projectiveLeftAction :
    MulAction (PGL(d, F))
      (IsoClass (d := d) (π := π) (φ := φ)
        (coefficientUniformizer_ne_zero (F := F) hπ)) where
  smul g q := projectiveReframe hπ g⁻¹ q
  one_smul q := by
    change projectiveReframe hπ (1 : PGL(d, F))⁻¹ q = q
    rw [inv_one, projectiveReframe_one]
  mul_smul g h q := by
    change projectiveReframe hπ ((g * h)⁻¹) q =
      projectiveReframe hπ g⁻¹ (projectiveReframe hπ h⁻¹ q)
    rw [mul_inv_rev, projectiveReframe_mul]

/-- An ordinary left projective matrix class acts by its inverse normalized reframe. -/
theorem projectiveLeftAction_mk_smul (g : GL (Fin d) F)
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    letI := projectiveLeftAction (F := F) (d := d) (φ := φ) hπ
    Matrix.ProjGenLinGroup.mk g • q =
      normalizedReframe hπ (matrixReframeEquiv d F g⁻¹) q := by
  change projectiveReframe hπ (Matrix.ProjGenLinGroup.mk g)⁻¹ q = _
  rw [← map_inv, projectiveReframe_mk]

end SheafDatum.IsoClass

end Langlands.DeligneFormalSpace
