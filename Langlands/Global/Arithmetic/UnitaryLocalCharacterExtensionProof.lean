import Langlands.Global.Arithmetic.UnitaryLocalCharacterExtensionStatement
import Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof
import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.HeckeNormTwist

/-!
# Unitary extension of an arbitrary finite local character

Match the character on integral units by a finite-order global character,
then correct the remaining unramified character by an imaginary norm power.
-/

noncomputable section

universe u

namespace Langlands.Global

/-- Every continuous unitary character of one finite completion extends to a
unitary character of the actual idele-class group. -/
theorem unitaryLocalCharacterExtension :
    UnitaryLocalCharacterExtensionStatement.{u} := by
  classical
  intro F _ _ v χ hχ
  let i : (v.adicCompletionIntegers F)ˣ →ₜ* (FiniteCompletion F v)ˣ :=
    { Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom with
      continuous_toFun := continuous_subtype_val.units_map _ }
  obtain ⟨η, ⟨n, hn, hη⟩, hηi⟩ :=
    integralUnitCharacterExtension F v (χ.comp i)
  let ηS : (w : {w // w ∈ ({v} : Finset (FinitePlace F))}) →
      (FiniteCompletion F w.1)ˣ →ₜ* ℂˣ := fun ⟨w, hw⟩ => by
    have hwv := Finset.mem_singleton.mp hw
    subst w
    exact η
  have hηS : ∀ w, ηS w ^ n = 1 := by
    rintro ⟨w, hw⟩
    have hwv := Finset.mem_singleton.mp hw
    subst w
    exact hη
  obtain ⟨ψ, hψ, hψS, _⟩ := finiteOrderCharacterPrescription_proof
    F {v} n hn ηS 1 hηS (by
      apply ContinuousMonoidHom.ext
      intro a
      rw [ContinuousMonoidHom.pow_apply]
      exact one_pow n)
  have hψv : ψ.finiteComponent v = η :=
    hψS ⟨v, Finset.mem_singleton_self v⟩
  have hψunitary : ψ.IsUnitary := by
    intro a
    apply Complex.norm_eq_one_of_pow_eq_one (n := 2 * n) _ (Nat.mul_pos (by decide) hn).ne'
    have ha := DFunLike.congr_fun hψ a
    have hp : (ψ a) ^ (2 * n) = 1 := by
      simpa only [ContinuousMonoidHom.pow_apply, ContinuousMonoidHom.one_toFun] using ha
    exact congrArg Units.val hp
  let δ := χ / ψ.finiteComponent v
  have hδ : ∀ a, ‖(δ a : ℂ)‖ = 1 := by
    intro a
    change ‖((χ a / ψ.finiteComponent v a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_div_eq_div_val]
    change ‖(χ a : ℂ) / (ψ (finiteClassInclusion F v a) : ℂ)‖ = 1
    rw [norm_div, hχ a, hψunitary, div_self one_ne_zero]
  have hδU : ∀ a : (FiniteCompletion F v)ˣ,
      a ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units → δ a = 1 := by
    intro a ha
    let b : (v.adicCompletionIntegers F)ˣ :=
      { val := ⟨a.val, ha.1⟩
        inv := ⟨(a⁻¹).val, ha.2⟩
        val_inv := Subtype.ext a.val_inv
        inv_val := Subtype.ext a.inv_val }
    have hib : i b = a := Units.ext rfl
    have hηa : η a = χ a := by
      rw [← hib]
      exact hηi b
    change χ a / ψ.finiteComponent v a = 1
    rw [hψv, hηa, div_self']
  obtain ⟨t, ht⟩ :=
    HeckeCharacter.exists_unitaryNormPower_finiteComponent v δ hδ hδU
  refine ⟨ψ * HeckeCharacter.unitaryNormPower F t, ?_, ?_⟩
  · intro a
    change ‖(ψ a : ℂ) * (HeckeCharacter.unitaryNormPower F t a : ℂ)‖ = 1
    rw [norm_mul, hψunitary, HeckeCharacter.unitaryNormPower_isUnitary, one_mul]
  · rw [HeckeCharacter.finiteComponent_mul, ht]
    exact mul_div_cancel _ _

end Langlands.Global
