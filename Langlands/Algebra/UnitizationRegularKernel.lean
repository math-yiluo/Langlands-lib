import Mathlib.Algebra.Algebra.Unitization
import Mathlib.RingTheory.Ideal.Maps

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationRegularKernel

universe uR uA

variable (R : Type uR) (A : Type uA)
variable [CommRing R] [NonUnitalRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]
variable [Module (Unitization R A) A]

/-- The actual regular unitization module identifies with the scalar-projection
kernel when its action satisfies the coordinate formula. -/
def regularKernelEquiv
    (hsmul : ∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) :
    A ≃ₗ[Unitization R A] RingHom.ker (Unitization.fstHom R A) where
  toFun a := ⟨Unitization.inr a, by
    change (Unitization.inr a : Unitization R A).fst = 0
    rfl⟩
  invFun x := x.val.snd
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Unitization.ext
    · change 0 = x.val.fst
      exact x.property.symm
    · rfl
  map_add' a b := by
    apply Subtype.ext
    exact Unitization.inr_add R a b
  map_smul' u a := by
    apply Subtype.ext
    apply Unitization.ext
    · simp
    · change u • a = (u * Unitization.inr a).snd
      simp [hsmul]

variable (hsmul : ∀ (u : Unitization R A) (a : A),
  u • a = u.fst • a + u.snd * a)

@[simp]
theorem regularKernelEquiv_apply_coe (a : A) :
    (regularKernelEquiv R A hsmul a : Unitization R A) = Unitization.inr a :=
  rfl

@[simp]
theorem regularKernelEquiv_apply_fst (a : A) :
    (regularKernelEquiv R A hsmul a : Unitization R A).fst = 0 :=
  rfl

@[simp]
theorem regularKernelEquiv_apply_snd (a : A) :
    (regularKernelEquiv R A hsmul a : Unitization R A).snd = a :=
  rfl

@[simp]
theorem regularKernelEquiv_symm_apply
    (x : RingHom.ker (Unitization.fstHom R A)) :
    (regularKernelEquiv R A hsmul).symm x = x.val.snd :=
  rfl

end Langlands.Algebra.UnitizationRegularKernel
