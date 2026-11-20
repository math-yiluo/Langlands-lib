import Langlands.Representation.Archimedean.GKModule
import Langlands.Representation.Archimedean.UnitaryWhittakerMultiplicityOneStatement

/-! # Admissibility for the unitary subgroup in the units model -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Operator

namespace Langlands.Archimedean

universe uF uE
variable (𝕜 : Type uF) [RCLike 𝕜] (n : ℕ)

/-- A unitary matrix gives the same element of the compact subgroup of units. -/
def matrixUnitaryToCompact : Matrix.unitaryGroup (Fin n) 𝕜 →* unitaryCompact 𝕜 n where
  toFun k := ⟨Unitary.toUnits k, k.property⟩
  map_one' := Subtype.ext (Unitary.toUnits.map_one)
  map_mul' k l := Subtype.ext (Unitary.toUnits.map_mul k l)

@[simp] theorem coe_matrixUnitaryToCompact (k : Matrix.unitaryGroup (Fin n) 𝕜) :
    (matrixUnitaryToCompact 𝕜 n k : Langlands.GeneralLinear n 𝕜) = Unitary.toUnits k := rfl

theorem continuous_matrixUnitaryToCompact : Continuous (matrixUnitaryToCompact 𝕜 n) := by
  have h : Continuous (Unitary.toUnits : Matrix.unitaryGroup (Fin n) 𝕜 →
      Langlands.GeneralLinear n 𝕜) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, (continuous_star.comp continuous_subtype_val).congr fun _ => rfl⟩
  exact h.subtype_mk _

/-- Admissibility of the included matrix unitary action implies admissibility
for the subgroup used by the smooth Whittaker uniqueness statement. -/
def UnitaryCompactAdmissibilityStatement : Prop :=
  ∀ (𝕜 : Type uF) [RCLike 𝕜] (n : ℕ)
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (π : Langlands.GeneralLinear n 𝕜 →* (E →L[ℂ] E)),
    IsAdmissibleGKModule (linearRepresentation (π.comp Unitary.toUnits)) →
      IsAdmissible π (unitaryCompact 𝕜 n)

theorem unitaryCompactAdmissibility : UnitaryCompactAdmissibilityStatement.{uF,uE} := by
  intro 𝕜 _ n E _ _ π hπ d τ hτ
  let τ' := τ.comp (matrixUnitaryToCompact 𝕜 n)
  let ρ := linearRepresentation (π.comp Unitary.toUnits)
  let L : intertwiners π (unitaryCompact 𝕜 n) d τ →ₗ[ℂ] gkIntertwiners ρ d τ' :=
    { toFun T := ⟨T.val, fun k x => T.property (matrixUnitaryToCompact 𝕜 n k) x⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let : FiniteDimensional ℂ (gkIntertwiners ρ d τ') :=
    hπ d τ' (hτ.comp (continuous_matrixUnitaryToCompact 𝕜 n))
  exact Module.Finite.of_injective L (fun _ _ h =>
    Subtype.ext (congrArg (fun T : gkIntertwiners ρ d τ' => T.val) h))

/-- Proportionality of smooth Whittaker functionals restricts to their
values on a prescribed algebraic carrier. -/
theorem proportional_whittakerRestrictions_of_unitaryUniqueness
    {L : Type} [RCLike L] (hUnique : UnitaryWhittakerMultiplicityOneOver.{uE} L)
    (r : ℕ) {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : Langlands.GeneralLinear (r + 1) L →* (E →L[ℂ] E))
    (hcont : IsContinuousRepresentation π)
    (hinner : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (hirr : IsTopologicallyIrreducible π)
    (hAdm : IsAdmissibleGKModule (linearRepresentation (π.comp Unitary.toUnits)))
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter L)
    (ℓ₀ ℓ₁ : smoothVectors (matrixModel L (r + 1)) π →ₗ[ℂ] ℂ)
    (h₀ : IsWhittakerFunctional (matrixModel L (r + 1)) π
      (Langlands.GeneralLinear.upperUnipotent (r + 1) L) (Langlands.Whittaker.standardCharacter ψ r) ℓ₀)
    (h₁ : IsWhittakerFunctional (matrixModel L (r + 1)) π
      (Langlands.GeneralLinear.upperUnipotent (r + 1) L) (Langlands.Whittaker.standardCharacter ψ r) ℓ₁)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (j : V →ₗ[ℂ] smoothVectors (matrixModel L (r + 1)) π) (hn : ℓ₀.comp j ≠ 0) :
    ∃ c : ℂ, ℓ₁.comp j = c • ℓ₀.comp j := by
  have hz : ℓ₀ ≠ 0 := fun h => hn (by rw [h, LinearMap.zero_comp])
  obtain ⟨c, hc⟩ := hUnique r E π hcont hinner hirr
    (unitaryCompactAdmissibility L (r + 1) E π hAdm) ψ ℓ₀ ℓ₁ h₀ h₁ hz
  exact ⟨c, LinearMap.ext fun v => congrArg (fun T => T (j v)) hc⟩

end Langlands.Archimedean
