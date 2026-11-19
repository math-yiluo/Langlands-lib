import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Module.Projective
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Lifting signs on an involutive lattice -/

universe u

namespace Langlands.LinearAlgebra

/-- A sign functional vanishing on the negative eigenspace of a lattice
involution lifts to an invariant integer-valued functional. -/
def InvolutiveLatticeSignStatement : Prop :=
  ∀ (Λ : Type u) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (s : Λ ≃ₗ[ℤ] Λ), (∀ a, s (s a) = a) →
    ∀ c : Λ →ₗ[ℤ] ZMod 2, (∀ a, s a = -a → c a = 0) →
      ∃ m : Λ →ₗ[ℤ] ℤ, (∀ a, m (s a) = m a) ∧ ∀ a, (m a : ZMod 2) = c a

theorem involutiveLatticeSign : InvolutiveLatticeSignStatement.{u} := by
  intro Λ _ _ _ s hs c hc
  let d : Λ →ₗ[ℤ] Λ := s.toLinearMap + LinearMap.id
  have hk : LinearMap.ker d ≤ LinearMap.ker c := by
    intro a ha
    have ha' : s a + a = 0 := LinearMap.mem_ker.mp ha
    exact LinearMap.mem_ker.mpr (hc a (add_eq_zero_iff_eq_neg.mp ha'))
  let c' : LinearMap.range d →ₗ[ℤ] ZMod 2 :=
    ((LinearMap.ker d).liftQ c hk).comp d.quotKerEquivRange.symm.toLinearMap
  let z : ℤ →ₗ[ℤ] ZMod 2 := (Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap
  let : Module.Finite ℤ (LinearMap.range d) := Module.Finite.range d
  let : Module.IsTorsionFree ℤ (LinearMap.range d) :=
    Function.Injective.moduleIsTorsionFree (LinearMap.range d).subtype
      Subtype.val_injective (fun _ _ => rfl)
  obtain ⟨m, hm⟩ := Module.projective_lifting_property z c' ZMod.intCast_surjective
  refine ⟨m.comp d.rangeRestrict, fun a => ?_, fun a => ?_⟩
  · have hd : d (s a) = d a := by
      change s (s a) + s a = s a + a
      rw [hs, add_comm]
    exact congrArg m (Subtype.ext hd)
  · have hq : d.quotKerEquivRange ((LinearMap.ker d).mkQ a) = d.rangeRestrict a :=
      Subtype.ext rfl
    calc
      _ = c' (d.rangeRestrict a) := LinearMap.congr_fun hm (d.rangeRestrict a)
      _ = c a := by
        change ((LinearMap.ker d).liftQ c hk) (d.quotKerEquivRange.symm (d.rangeRestrict a)) = c a
        rw [← hq, LinearEquiv.symm_apply_apply]
        rfl

end Langlands.LinearAlgebra
