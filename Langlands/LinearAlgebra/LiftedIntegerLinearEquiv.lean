import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Module.NatInt

/-! # Additive equivalences of modules over the lifted integers -/

universe u v w

namespace Langlands.LinearAlgebra

/-- Additive equivalences between lifted-integer modules are linear for
any supplied module structures, since scalar multiplication is integer multiplication. -/
def liftedIntLinearEquivOfAddEquiv
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module (ULift.{u} ℤ) M] [Module (ULift.{u} ℤ) N] (e : M ≃+ N) :
    M ≃ₗ[ULift.{u} ℤ] N where
  __ := e
  map_smul' r x := by
    have hr : (r.down : ULift.{u} ℤ) = r := by cases r; rfl
    dsimp only [RingHom.id_apply]
    rw [← hr, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact map_zsmul e r.down x

end Langlands.LinearAlgebra
