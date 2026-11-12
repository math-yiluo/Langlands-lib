import Langlands.Representation.Smooth.RenardSigmaCompactSchurProof

/-! # Central characters and scalar categorical-center actions -/

noncomputable section

universe u v w

namespace Langlands.Renard.Smooth

/-- Renard III.1.10: central characters, disjointness and the categorical center. -/
theorem centralCharacter : CentralCharacterStatement.{u, v, w} := by
  classical
  intro G _ _ _ _ _ _ _ Z hZ
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ π hπ hi
    let := hi
    let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    let T (z : Z) : π.IntertwiningMap π :=
      { toLinearMap := π z
        isIntertwining' := fun g => by
          change π (z : G) * π g = π g * π (z : G)
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ z.property) g] }
    have hs (z : Z) := (sigmaCompactSchur.{u, v, w} G V π hπ hi).1 (T z)
    choose c hc using hs
    have act (z : Z) (y : V) : π (z : G) y = c z • y :=
      congrArg (fun f : π.IntertwiningMap π => f y) (hc z)
    have c_one : c 1 = 1 := by
      apply smul_left_injective ℂ hx
      dsimp only
      rw [← act]
      simp
    have c_mul (z t : Z) : c (z * t) = c z * c t := by
      apply smul_left_injective ℂ hx
      dsimp only
      rw [← act]
      change π ((z : G) * (t : G)) x = _
      rw [map_mul, Module.End.mul_apply, act, act, smul_smul]
    have c_ne (z : Z) : c z ≠ 0 := by
      intro hz
      have h := c_mul z⁻¹ z
      rw [inv_mul_cancel, c_one, hz, mul_zero] at h
      exact one_ne_zero h
    exact ⟨{ toFun := fun z => Units.mk0 (c z) (c_ne z)
             map_one' := Units.ext c_one
             map_mul' := fun z t => Units.ext (c_mul z t) }, act⟩
  · intro V _ _ π₁ W _ _ π₂ χ₁ χ₂ hne h₁ h₂ f
    obtain ⟨z, hz⟩ : ∃ z, χ₁ z ≠ χ₂ z := Function.ne_iff.mp
      (fun h => hne (MonoidHom.ext fun z => congrFun h z))
    have hz' : (χ₁ z : ℂ) ≠ (χ₂ z : ℂ) := fun h => hz (Units.ext h)
    ext x
    have h : (χ₁ z : ℂ) • f x = (χ₂ z : ℂ) • f x := by
      rw [← map_smul, ← h₁, f.isIntertwining, h₂]
    have hzero : ((χ₁ z : ℂ) - (χ₂ z : ℂ)) • f x = 0 := by
      rw [sub_smul, h, sub_self]
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz')
  · intro z V hi
    obtain ⟨c, hc⟩ := (sigmaCompactSchur.{u, v, w} G V V.representation V.isSmooth hi).1
      (SmoothRep.hom (z.app V))
    exact ⟨c, fun x => congrArg (fun f : V.representation.IntertwiningMap
      V.representation => f x) hc⟩

end Langlands.Renard.Smooth
