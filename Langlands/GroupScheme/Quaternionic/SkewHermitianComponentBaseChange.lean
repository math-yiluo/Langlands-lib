import Langlands.GroupScheme.Quaternionic.SkewHermitianQuadraticComponent
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Scalar extension of the symmetric component of a skew-hermitian form -/

noncomputable section

universe u v

open TensorProduct LinearMap
open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

section TensorMaps

variable {F R : Type u} [Field F] [Field R] [Algebra F R]
variable {W : Type v} [AddCommGroup W] [Module F W]
variable {M : Type*} [AddCommGroup M] [Module F M] [Module R M] [IsScalarTower F R M]

private def tensorLift (f : W →ₗ[F] M) : R ⊗[F] W →ₗ[R] M :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton R (W →ₗ[F] M) f)

private theorem tensorLift_tmul (f : W →ₗ[F] M) (r : R) (w : W) :
    tensorLift (R := R) f (r ⊗ₜ[F] w) = r • f w := rfl

variable {E : Type u} [Field E] [Algebra F E] [Module E W] [IsScalarTower F E W]
  [Algebra E R] [IsScalarTower F E R]

private def tensorProjection : R ⊗[F] W →ₗ[R] R ⊗[E] W :=
  tensorLift ((TensorProduct.mk E R W 1).restrictScalars F)

private theorem tensorProjection_tmul (r : R) (w : W) :
    tensorProjection (F := F) (E := E) (r ⊗ₜ[F] w) = r ⊗ₜ[E] w := by
  rw [tensorProjection, tensorLift_tmul]
  change r • ((1 : R) ⊗ₜ[E] w) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end TensorMaps

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (Q : QuatData F D)

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E

/-- Left multiplication by an embedded field element multiplies the first coordinate. -/
theorem fst_ι_mul (a : E) (z : D) : Q.fst (Q.ι a * z) = a * Q.fst z := by
  have h : Q.ι a * Q.j = Q.j * Q.ι (κ a) := by
    have h := Q.j_mul_ι (κ a)
    rw [SU3Root.conjugation_involutive] at h
    exact h.symm
  conv_lhs => rw [← Q.decompose z, mul_add, ← mul_assoc (Q.ι a), h, mul_assoc,
    ← map_mul, ← map_mul]
  exact Q.fst_mk _ _

variable {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

private theorem embeddedScalarTower :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    IsScalarTower F E V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  exact ⟨fun a b x => by
    change (Q.ι (a • b)) • x = a • (Q.ι b • x)
    rw [map_smul, smul_assoc]⟩

private def firstComponentAt (y : V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    V →ₗ[E] E := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  refine { toFun := fun x => Q.fst (B x y), map_add' := ?_, map_smul' := ?_ }
  · intro x x'
    rw [B.add_left, map_add]
  · intro a x
    change Q.fst (B (Q.ι a • x) y) = a * Q.fst (B x y)
    rw [B.smul_left, Q.fst_ι_mul]

/-- After extending scalars to a field containing the quadratic subfield, a value equal to
  the distinguished pure quaternion yields an isotropic vector of the symmetric component. -/
theorem exists_isotropic_component_of_representation (R : Type u) [Field R] [Algebra F R]
    [Algebra (field Q.c) R] [IsScalarTower F (field Q.c) R] (t : R ⊗[F] V)
    (ht : LinearMap.BilinMap.baseChange R B.toBilin t t = (1 : R) ⊗ₜ[F] Q.x) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    ∃ w : R ⊗[E] V, w ≠ 0 ∧ LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar) w w = 0 := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : IsScalarTower F E V := Q.embeddedScalarTower
  let p : R ⊗[F] V →ₗ[R] R ⊗[E] V := tensorProjection
  let H := LinearMap.BilinForm.baseChange R (Q.symmetricComponent B hbar)
  let B_R := LinearMap.BilinMap.baseChange R B.toBilin
  let f₁ := (Algebra.linearMap E R).restrictScalars F ∘ₗ Q.fst
  let f₂ := (Algebra.linearMap E R).restrictScalars F ∘ₗ (κ).toLinearMap ∘ₗ Q.snd
  have hcomp : H.compl₁₂ p p = B_R.compr₂ (tensorLift (R := R) f₂) := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have tfirst : ∀ (r : R) (x : V),
        H (p (r ⊗ₜ[F] x)) (p v) = tensorLift (R := R) f₂ (B_R (r ⊗ₜ[F] x) v) := by
      intro r x
      have he : (H (p (r ⊗ₜ[F] x))).comp p =
          (tensorLift (R := R) f₂).comp (B_R (r ⊗ₜ[F] x)) := by
        apply AlgebraTensorModule.ext
        intro s y
        simp only [LinearMap.comp_apply, p, tensorProjection_tmul, H,
          LinearMap.BilinForm.baseChange_tmul, B_R, LinearMap.BilinMap.baseChange_tmul,
          tensorLift_tmul, f₂, symmetricComponent_apply, Algebra.smul_def,
          LinearMap.coe_restrictScalars, AlgEquiv.toLinearMap_apply, Algebra.linearMap_apply,
          Algebra.algebraMap_self_apply]
        ring
      exact LinearMap.congr_fun he v
    have he : (H.flip (p v)).comp p = (tensorLift (R := R) f₂).comp (B_R.flip v) :=
      AlgebraTensorModule.ext tfirst
    exact LinearMap.congr_fun he u
  have hzero : H (p t) (p t) = 0 := by
    have he := LinearMap.congr_fun (LinearMap.congr_fun hcomp t) t
    change H (p t) (p t) = tensorLift (R := R) f₂ (B_R t t) at he
    rw [he, ht, tensorLift_tmul, one_smul]
    have hx : Q.snd Q.x = 0 := by rw [← Q.ι_root, Q.snd_ι]
    simp only [f₂, LinearMap.comp_apply, hx, _root_.map_zero]
  have hp : p t ≠ 0 := by
    intro hz
    have hf (y : V) :
        (tensorLift (R := R) f₁).comp (B_R.flip ((1 : R) ⊗ₜ[F] y)) =
          (tensorLift (F := E) (R := R) ((Algebra.linearMap E R).comp (Q.firstComponentAt B y))).comp p := by
      apply AlgebraTensorModule.ext
      intro r x
      simp only [comp_apply, flip_apply, p, tensorProjection_tmul, B_R, LinearMap.BilinMap.baseChange_tmul,
        mul_one, tensorLift_tmul, f₁, LinearMap.coe_restrictScalars, Algebra.linearMap_apply]
      rfl
    have hg : (tensorLift (R := R) f₁).comp (B_R t) = 0 := by
      apply AlgebraTensorModule.ext
      intro r y
      have h := LinearMap.congr_fun (hf y) t
      simp only [comp_apply, flip_apply, hz, LinearMap.map_zero] at h
      have he : r ⊗ₜ[F] y = r • ((1 : R) ⊗ₜ[F] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he, comp_apply, LinearMap.zero_apply, _root_.map_smul, _root_.map_smul, h, smul_zero]
    have h := LinearMap.congr_fun hg t
    rw [comp_apply, LinearMap.zero_apply, ht, tensorLift_tmul, one_smul] at h
    change algebraMap E R (Q.fst Q.x) = 0 at h
    rw [← Q.ι_root, Q.fst_ι] at h
    have hroot : (root : E) = 0 := (algebraMap E R).injective (h.trans (_root_.map_zero _).symm)
    have hx : Q.x = 0 := by rw [← Q.ι_root, hroot, _root_.map_zero]
    have hb := Q.basis.ne_zero 1
    rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at hb
    exact hb hx
  exact ⟨p t, hp, hzero⟩

end Langlands.GroupScheme.KneserThree.QuatData
