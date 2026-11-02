import Langlands.Global.Arithmetic.CMCharacterAssemblyStatement

noncomputable section

universe u v

namespace Langlands.Global

open NumberField

/-- Assemble the regular CM character on the existing arithmetic interfaces. -/
theorem cmRegularUnitPrescriptionOfInputs :
    CMRegularUnitPrescriptionOfInputsStatement.{u,v} := by
  intro hInfinity hFinite hUnits E _ _ _ hE K _ _ _ ι τ a ha hreg S hS η
  classical
  have hlocal : ∀ w : {w // w ∈ S},
      ∃ ξ : (FiniteCompletion K w.1)ˣ →ₜ* ℂˣ,
        (∃ n : ℕ, 0 < n ∧ ξ ^ n = 1) ∧
        ∀ b : (w.1.adicCompletionIntegers K)ˣ,
          ξ (Units.map (w.1.adicCompletionIntegers K).subtype.toMonoidHom b) = η w b :=
    fun w => hUnits K w.1 (η w)
  choose ξ hξorder hξunits using hlocal
  obtain ⟨ψ, hψorder, hψsd, hψinf, hψfin⟩ := hFinite K S hS ξ hξorder
  obtain ⟨m, μ, hm, hμsd, hμinf, hμunr⟩ := hInfinity K a ha
  refine ⟨m, μ * ψ, hm, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [ContinuousMonoidHom.mul_apply, hμsd, hψsd, mul_inv]
  · change μ.atInfinity * ψ.atInfinity = _
    rw [hμinf, hψinf]
    ext x
    exact mul_one _
  · have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    intro σ ρ h
    apply hreg
    exact mul_left_cancel₀ hm0 h
  · intro w b
    have hb :
        Units.map (w.1.adicCompletionIntegers K).subtype.toMonoidHom b ∈
          (Submonoid.ofClass (w.1.adicCompletionIntegers K)).units := by
      exact ⟨b.val.property, b.inv.property⟩
    rw [HeckeCharacter.finiteComponent_mul, ContinuousMonoidHom.mul_apply,
      hμunr w.1 _ hb, hψfin w, one_mul, hξunits w b]

end Langlands.Global
