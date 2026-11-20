import Langlands.BaseChange.LocalGaloisStabilizer
import Mathlib.GroupTheory.OrderOfElement

/-! # Period of a local representation with trivial Galois stabilizer -/

noncomputable section

universe uF uE uV

set_option autoImplicit false

namespace Langlands.BaseChange

/-- A power fixes a representation with trivial Galois stabilizer up to
equivalence precisely when the automorphism order divides the exponent. -/
def SigmaOrbitPeriodStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear n E) V),
    HasTrivialGaloisStabilizer F τ →
    ∀ i : ℕ,
      Nonempty (Representation.Equiv τ (τ.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) ↔
        orderOf σ ∣ i

/-- Translate trivial stabilizer to the exponent-divisibility condition. -/
theorem conjugate_equiv_iff_orderOf_dvd : SigmaOrbitPeriodStatement.{uF, uE, uV} := by
  intro F E _ _ _ σ n V _ _ τ hτ i
  constructor
  · intro he
    exact orderOf_dvd_iff_pow_eq_one.mpr (by_contra fun h => hτ (σ ^ i) h he)
  · intro hi
    rw [(orderOf_dvd_iff_pow_eq_one).mp hi]
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => ?_)⟩
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, entrywiseAut_one_apply]

end Langlands.BaseChange
