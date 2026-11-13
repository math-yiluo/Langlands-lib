import Langlands.Geometry.Building.SymmetricRelativeDerivativeRoots
import Langlands.Geometry.Building.AffineSimpleRootGram
import Langlands.Geometry.Building.AffineChamberAction

/-! # Root lengths and symmetric derivative pairings -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ)

/-- Every derivative root has the same squared length in the full coroot form. -/
def HasEqualDerivativeLengths : Prop :=
  ∀ a b : derivativeRoots Ψ,
    hΨ.corootForm a.val a.val = hΨ.corootForm b.val b.val

include hΨ

omit hΨ in
/-- A root-preserving affine map permutes all coroot vectors. -/
theorem linear_mem_corootSet {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) {v : V} (hv : v ∈ corootSet Ψ) :
    e.linear v ∈ corootSet Ψ := by
  obtain ⟨ψ, hψ, hv⟩ := hv
  exact ⟨ψ.comp (e.symm : A →ᵃ[ℝ] A),
    (comp_mem_iff (inv_mem he) ψ).mpr hψ, hv.map he⟩

/-- Pullback by a root-preserving affine map preserves the full coroot form. -/
theorem corootForm_comp_linear {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (α β : Module.Dual ℝ V) :
    hΨ.corootForm (α.comp e.linear.toLinearMap) (β.comp e.linear.toLinearMap) =
      hΨ.corootForm α β := by
  let T := hΨ.finite_corootSet.toFinset
  have hf : ∀ v ∈ T, e.linear v ∈ T := by
    intro v hv
    exact hΨ.finite_corootSet.mem_toFinset.mpr
      (linear_mem_corootSet he (hΨ.finite_corootSet.mem_toFinset.mp hv))
  have hg : ∀ v ∈ T, e.linear.symm v ∈ T := by
    intro v hv
    exact hΨ.finite_corootSet.mem_toFinset.mpr
      (linear_mem_corootSet (inv_mem he)
        (hΨ.finite_corootSet.mem_toFinset.mp hv))
  have hs : ∑ v ∈ T, α (e.linear v) * β (e.linear v) =
      ∑ v ∈ T, α v * β v := Finset.sum_nbij' e.linear e.linear.symm hf hg
    (fun v _ => e.linear.symm_apply_apply v)
    (fun v _ => e.linear.apply_symm_apply v)
    (fun v (_ : v ∈ T) => (rfl : α (e.linear v) * β (e.linear v) =
      α (e.linear v) * β (e.linear v)))
  exact hs

/-- The squared length of an affine root is invariant under a root-preserving
affine change of variables. -/
theorem corootForm_linear_comp {e : A ≃ᵃ[ℝ] A}
    (he : e ∈ rootStabilizer Ψ) (ψ η : A →ᵃ[ℝ] ℝ) :
    hΨ.corootForm (ψ.comp (e : A →ᵃ[ℝ] A)).linear
      (η.comp (e : A →ᵃ[ℝ] A)).linear =
        hΨ.corootForm ψ.linear η.linear :=
  hΨ.corootForm_comp_linear he ψ.linear η.linear

/-- Equal lengths of every derivative root force symmetry of the full
root-coroot evaluation pairing. -/
theorem hasSymmetricDerivativePairing_of_equal_lengths
    (hlen : hΨ.HasEqualDerivativeLengths) :
    hΨ.HasSymmetricDerivativePairing := by
  intro a b
  have ha := hΨ.two_mul_corootForm (hΨ.isCoroot_derivativeCoroot a) b.val
  have hb := hΨ.two_mul_corootForm (hΨ.isCoroot_derivativeCoroot b) a.val
  simp only [hΨ.linear_derivativeRootLift] at ha hb
  rw [hΨ.corootForm_comm b.val a.val] at ha
  rw [hlen b a] at hb
  have hpos := hΨ.corootForm_self_pos (hΨ.derivativeRootLift_mem a)
  simp only [hΨ.linear_derivativeRootLift] at hpos
  nlinarith

end IsAffineRootSystemWithRankZero

end Langlands.Geometry.Building.AffineRootSystem
