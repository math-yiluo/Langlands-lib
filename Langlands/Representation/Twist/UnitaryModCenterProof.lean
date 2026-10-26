import Langlands.Representation.Twist.UnitaryModCenterStatement
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Representation.Twist.AlgebraProof

/-! # Unitary twists preserve analytic coefficients modulo the center -/

noncomputable section

namespace Langlands

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace UnitaryCentralCharacter

variable {ρ : Representation ℂ G V}

/-- Multiply the given scalar central character by the restriction of a
norm-one open-kernel character to the actual center. -/
def unitaryTwist (c : UnitaryCentralCharacter ρ) (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1) :
    UnitaryCentralCharacter (twist χ ρ) where
  character := (χ.comp (Subgroup.center G).subtype) * c.character
  isOpen_ker := by
    have hle :
        (χ.comp (Subgroup.center G).subtype).ker ⊓ c.character.ker ≤
          ((χ.comp (Subgroup.center G).subtype) * c.character).ker := by
      intro z hz
      change χ z * c.character z = 1
      have hz1 := hz.1
      have hz2 := hz.2
      change χ z = 1 at hz1
      change c.character z = 1 at hz2
      rw [hz1, hz2, one_mul]
    exact Subgroup.isOpen_mono hle
      ((hχ.preimage continuous_subtype_val).inter c.isOpen_ker)
  norm_eq_one := by
    intro z
    change ‖((χ z : ℂˣ) : ℂ) * (c.character z : ℂ)‖ = 1
    rw [norm_mul, hu, c.norm_eq_one, one_mul]
  acts := by
    intro z v
    change (χ z : ℂ) • ρ z v =
      ((χ z : ℂ) * (c.character z : ℂ)) • v
    rw [c.acts, smul_smul]

/-- Unitary twisting leaves the norm of every algebraic coefficient unchanged
on the full central quotient. -/
theorem coefficientNorm_unitaryTwist (c : UnitaryCentralCharacter ρ)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    (ℓ : Module.Dual ℂ V) (v : V) :
    (c.unitaryTwist χ hχ hu).coefficientNorm ℓ v = c.coefficientNorm ℓ v := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change ‖ℓ ((χ g : ℂ) • ρ g v)‖ = ‖ℓ (ρ g v)‖
    rw [map_smul, norm_smul, hu, one_mul]

end UnitaryCentralCharacter

variable [MeasurableSpace (G ⧸ Subgroup.center G)]
variable [BorelSpace (G ⧸ Subgroup.center G)]

theorem isSquareIntegrableModCenter_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    {ρ : Representation ℂ G V}
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (hρ : IsSquareIntegrableModCenter ρ μ) :
    IsSquareIntegrableModCenter (twist χ ρ) μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨(isAdmissible_twist_iff χ ρ hχ).mpr hρ, c.unitaryTwist χ hχ hu, ?_⟩
  intro ℓ v
  rw [c.coefficientNorm_unitaryTwist χ hχ hu]
  exact hc (smoothContragredientTwistEquiv χ ρ hχ ℓ) v

omit [BorelSpace (G ⧸ Subgroup.center G)] in
theorem isTemperedModCenter_unitaryTwist
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    (hu : ∀ g : G, ‖(χ g : ℂ)‖ = 1)
    {ρ : Representation ℂ G V}
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (hρ : IsTemperedModCenter ρ μ) :
    IsTemperedModCenter (twist χ ρ) μ := by
  obtain ⟨hρ, c, hc⟩ := hρ
  refine ⟨(isAdmissible_twist_iff χ ρ hχ).mpr hρ, c.unitaryTwist χ hχ hu, ?_⟩
  intro ℓ v ε hε
  rw [c.coefficientNorm_unitaryTwist χ hχ hu]
  exact hc (smoothContragredientTwistEquiv χ ρ hχ ℓ) v ε hε

/-- The entire closed statement, with independent group and carrier universes. -/
theorem unitaryTwistModCenter : UnitaryTwistModCenterStatement.{uG,uV} := by
  intro G _ _ _ _ _ V _ _ μ _ ρ χ hχ hu
  have hχinv : IsOpen ((χ⁻¹).ker : Set G) := by
    have hk : (χ⁻¹).ker = χ.ker := by
      ext g
      simp
    simpa only [hk] using hχ
  have huinv : ∀ g : G, ‖(χ⁻¹ g : ℂ)‖ = 1 := by
    intro g
    simpa using hu g
  constructor
  · constructor
    · intro h
      simpa only [twist_inv_twist] using
        isSquareIntegrableModCenter_unitaryTwist χ⁻¹ hχinv huinv μ h
    · exact isSquareIntegrableModCenter_unitaryTwist χ hχ hu μ
  · constructor
    · intro h
      simpa only [twist_inv_twist] using
        isTemperedModCenter_unitaryTwist χ⁻¹ hχinv huinv μ h
    · exact isTemperedModCenter_unitaryTwist χ hχ hu μ

end Langlands
