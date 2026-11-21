import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Lifting the fixed elements of the modified Dieudonné module -/

noncomputable section

namespace Langlands.FormalGroup.Drinfeld

variable {O M N : Type*} [CommRing O] [AddCommGroup M] [AddCommGroup N]
  [Module O M] [Module O N]
variable (q : M →ₗ[O] N) {F : Module.End O M} {G : Module.End O N}

private theorem commutes_apply (hcomm : q.comp F = G.comp q) (x : M) :
    q (F x) = G (q x) :=
  LinearMap.congr_fun hcomm x

/-- The endomorphism induced on the kernel of an equivariant linear map. -/
def kernelEnd (hcomm : q.comp F = G.comp q) : Module.End O (LinearMap.ker q) :=
  F.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [commutes_apply q hcomm, hx, map_zero]

/-- An equivariant linear map restricts to the submodules of fixed elements. -/
def fixedSubmoduleMap (hcomm : q.comp F = G.comp q) : F.fixedSubmodule →ₗ[O] G.fixedSubmodule :=
  q.restrict fun x hx => by
    rw [LinearMap.mem_fixedSubmodule_iff] at hx ⊢
    rw [← commutes_apply q hcomm, hx]

variable (hcomm : q.comp F = G.comp q)

/-- Fixed elements lift uniquely under a surjection with a nilpotent kernel endomorphism. -/
def fixedSubmoduleLiftEquiv (hsurj : Function.Surjective q)
    (hnil : IsNilpotent (kernelEnd q hcomm)) : F.fixedSubmodule ≃ₗ[O] G.fixedSubmodule :=
  LinearEquiv.ofBijective (fixedSubmoduleMap q hcomm) (by
    let difference : Module.End O (LinearMap.ker q) := 1 - kernelEnd q hcomm
    have hdiff : Function.Bijective difference :=
      (Module.End.isUnit_iff _).mp hnil.isUnit_one_sub
    constructor
    · intro x y hxy
      have hq : q (x : M) = q (y : M) := congrArg Subtype.val hxy
      let z : LinearMap.ker q := ⟨(x : M) - (y : M), by
        rw [LinearMap.mem_ker, map_sub, hq, sub_self]⟩
      have hz : difference z = 0 := by
        apply Subtype.ext
        change ((x : M) - (y : M)) - F ((x : M) - (y : M)) = 0
        rw [map_sub, LinearMap.mem_fixedSubmodule_iff.mp x.prop,
          LinearMap.mem_fixedSubmodule_iff.mp y.prop, sub_self]
      have hz' : z = 0 := hdiff.injective (hz.trans (map_zero difference).symm)
      exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val hz'))
    · intro y
      obtain ⟨x, hx⟩ := hsurj (y : N)
      have he : F x - x ∈ LinearMap.ker q := by
        rw [LinearMap.mem_ker, map_sub, commutes_apply q hcomm, hx,
          LinearMap.mem_fixedSubmodule_iff.mp y.prop, sub_self]
      obtain ⟨z, hz⟩ := hdiff.surjective ⟨F x - x, he⟩
      have hz' : (z : M) - F (z : M) = F x - x := congrArg Subtype.val hz
      have hfix : x + (z : M) ∈ F.fixedSubmodule := by
        rw [LinearMap.mem_fixedSubmodule_iff, map_add]
        exact (sub_eq_sub_iff_add_eq_add.mp hz').symm.trans (add_comm _ _)
      refine ⟨⟨x + (z : M), hfix⟩, Subtype.ext ?_⟩
      change q (x + (z : M)) = (y : N)
      rw [map_add, hx, LinearMap.mem_ker.mp z.prop, add_zero])

@[simp]
theorem fixedSubmoduleLiftEquiv_apply (hsurj : Function.Surjective q)
    (hnil : IsNilpotent (kernelEnd q hcomm)) (x : F.fixedSubmodule) :
    (fixedSubmoduleLiftEquiv q hcomm hsurj hnil x : N) = q x := rfl

end Langlands.FormalGroup.Drinfeld
