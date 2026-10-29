import Langlands.Representation.Exponents.SmoothOpenKernelStatement

/-! # Open kernels of generalized characters of smooth representations -/

noncomputable section

namespace Langlands

universe uR uG uV

section Generic

variable {k : Type uR} [Field k]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- A generalized eigencharacter of a smooth action has open kernel. -/
theorem isOpen_ker_of_isGeneralizedEigencharacter
    (π : Representation k G V) (χ : G →* kˣ)
    (hπ : IsSmooth π) (hχ : IsGeneralizedEigencharacter π χ) :
    IsOpen (χ.ker : Set G) := by
  obtain ⟨r, v, hv, hgen⟩ := (isGeneralizedEigencharacter_iff π χ).mp hχ
  obtain ⟨K, hK⟩ := hπ v
  apply Subgroup.isOpen_mono (H₁ := K.toSubgroup) ?_ K.isOpen
  intro g hg
  have hfix : π g v = v := hK ⟨g, hg⟩
  have hdef : (π g - (χ g : k) • 1) v = (1 - (χ g : k)) • v := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hfix, sub_smul, one_smul]
  have hpow : ∀ m : ℕ, ((π g - (χ g : k) • 1) ^ m) v =
      (1 - (χ g : k)) ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hdef, smul_smul,
        pow_succ, mul_comm]
  have hz : (1 - (χ g : k)) ^ r = 0 := by
    have h := hgen g
    rw [hpow] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have hscalar : (χ g : k) = 1 := by
    by_contra hne
    exact (pow_ne_zero r (sub_ne_zero.mpr (Ne.symm hne))) hz
  change χ g = 1
  exact Units.ext hscalar

/-- The generic smoothness statement, with independent field, group and carrier
universes. -/
theorem smoothGeneralizedEigencharacterOpenKernel :
    SmoothGeneralizedEigencharacterOpenKernelStatement.{uR, uG, uV} := by
  intro k _ G _ _ _ V _ _ π χ hπ hχ
  exact isOpen_ker_of_isGeneralizedEigencharacter π χ hπ hχ

end Generic

end Langlands
