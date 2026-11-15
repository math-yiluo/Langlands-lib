import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# Maximally faithful proper quotients with an infinitesimal character

`MaximallyFaithfulAnnihilatorStatement`: let `π` be an action of a complex Lie algebra `L` on
`V` with an infinitesimal character, and let `R ≠ V` be a subspace such that the quotient
`V / R` is maximally faithful (`IsMaximallyFaithfulModulo π R`). Then every `u ∈ U(L)` that
annihilates `V / R` (that is, `u · v ∈ R` for all `v`) already annihilates `V`.

The proof (`maximallyFaithfulAnnihilator`): a central `z` annihilating `V / R` acts on `V` by a
scalar `c`; if `c ≠ 0`, then every `v = c⁻¹ (z · v)` lies in `R`, so `R = V`. Hence `z` acts
by `0`, and so does every element of the ideal these `z` generate, which by maximal
faithfulness contains `u`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uL uV

/-- **Maximally faithful proper quotients have the annihilator of the whole module.** If `π`
has an infinitesimal character, `R` is a proper subspace of `V`, and `V / R` is maximally
faithful, then every element of `U(L)` annihilating `V / R` annihilates `V`. -/
def MaximallyFaithfulAnnihilatorStatement : Prop :=
  ∀ (L : Type uL) [LieRing L] [LieAlgebra ℂ L] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : L →ₗ⁅ℂ⁆ Module.End ℂ V) (R : Submodule ℂ V),
    HasInfinitesimalCharacter π → R ≠ ⊤ → IsMaximallyFaithfulModulo π R →
      ∀ u : UniversalEnvelopingAlgebra ℂ L, (∀ v : V, envelopingAction π u v ∈ R) →
        envelopingAction π u = 0

namespace MaximallyFaithfulAnnihilator

variable {L : Type uL} [LieRing L] [LieAlgebra ℂ L] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A central element annihilating `V / R`, for a proper subspace `R`, acts by `0` on `V` when
`π` has an infinitesimal character. -/
theorem envelopingAction_eq_zero_of_center {π : L →ₗ⁅ℂ⁆ Module.End ℂ V} {R : Submodule ℂ V}
    (hπ : HasInfinitesimalCharacter π) (hR : R ≠ ⊤) {z : UniversalEnvelopingAlgebra ℂ L}
    (hz : z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L))
    (hzR : ∀ v : V, envelopingAction π z v ∈ R) : envelopingAction π z = 0 := by
  obtain ⟨c, hc⟩ := hπ z hz
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [hc, map_zero]
  · refine absurd (eq_top_iff.2 fun v _ => ?_) hR
    have h := R.smul_mem c⁻¹ (hzR v)
    rwa [hc, Module.algebraMap_end_apply, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h

/-- Proof of `MaximallyFaithfulAnnihilatorStatement`. -/
theorem envelopingAction_eq_zero {π : L →ₗ⁅ℂ⁆ Module.End ℂ V} {R : Submodule ℂ V}
    (hπ : HasInfinitesimalCharacter π) (hR : R ≠ ⊤) (hmf : IsMaximallyFaithfulModulo π R)
    {u : UniversalEnvelopingAlgebra ℂ L} (hu : ∀ v : V, envelopingAction π u v ∈ R) :
    envelopingAction π u = 0 := by
  have hspan : Ideal.span {z | z ∈ Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ L) ∧
      ∀ v : V, envelopingAction π z v ∈ R} ≤ RingHom.ker (envelopingAction π) := by
    refine Ideal.span_le.2 fun z hz => ?_
    exact RingHom.mem_ker.2 (envelopingAction_eq_zero_of_center hπ hR hz.1 hz.2)
  exact RingHom.mem_ker.1 (hspan (hmf u hu))

end MaximallyFaithfulAnnihilator

/-- **Maximally faithful proper quotients have the annihilator of the whole module.** -/
theorem maximallyFaithfulAnnihilator : MaximallyFaithfulAnnihilatorStatement.{uL, uV} :=
  fun _ _ _ _ _ _ _ _ hπ hR hmf _ hu =>
    MaximallyFaithfulAnnihilator.envelopingAction_eq_zero hπ hR hmf hu

end Langlands.Archimedean
