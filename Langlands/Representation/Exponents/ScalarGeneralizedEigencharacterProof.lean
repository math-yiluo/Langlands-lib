import Langlands.Representation.Exponents.ScalarGeneralizedEigencharacterStatement

/-! # Scalar generalized-character detection -/

noncomputable section

namespace Langlands

universe uG uC uV

section ScalarDetection

variable {G : Type uG} [Group G] {C : Type uC} [Group C]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} {z : C →* G} {ω χ : C →* ℂˣ}

theorem scalar_generalized_character_eq
    (hω : Classification.HasScalarCharacter ρ z ω)
    (hχ : IsGeneralizedEigencharacter (ρ.comp z) χ) : χ = ω := by
  obtain ⟨k, v, hv, hk⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  ext c
  have hρ : (ρ.comp z) c = (ω c : ℂ) • (1 : Module.End ℂ V) := by
    ext w
    exact hω c w
  have hzero : ((ω c : ℂ) - (χ c : ℂ)) ^ k • v = 0 := by
    simpa only [hρ, ← sub_smul, smul_pow, one_pow, LinearMap.smul_apply,
      Module.End.one_apply] using hk c
  exact (sub_eq_zero.mp (eq_zero_of_pow_eq_zero
    ((smul_eq_zero.mp hzero).resolve_right hv))).symm

theorem scalar_generalized_character_iff [Nontrivial V]
    (hω : Classification.HasScalarCharacter ρ z ω) :
    IsGeneralizedEigencharacter (ρ.comp z) χ ↔ χ = ω := by
  constructor
  · exact scalar_generalized_character_eq hω
  · rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact isGeneralizedEigencharacter_of_eigenvector _ _ hv (fun c => hω c v)

end ScalarDetection

section CharacterRestriction

variable {G : Type uG} [Monoid G] {C : Type uC} [Monoid C]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} {χ : G →* ℂˣ}

theorem isGeneralizedEigencharacter_comp (f : C →* G)
    (hχ : IsGeneralizedEigencharacter ρ χ) :
    IsGeneralizedEigencharacter (ρ.comp f) (χ.comp f) := by
  obtain ⟨k, v, hv, hk⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  exact (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, v, hv, fun c => hk (f c)⟩

end CharacterRestriction

/-- The exact generic scalar-detection proposition. -/
theorem scalarGeneralizedEigencharacterDetection :
    ScalarGeneralizedEigencharacterDetection.{uG,uC,uV} := by
  constructor
  · intro G _ C _ V _ _ ρ z ω χ hω hχ
    exact scalar_generalized_character_eq hω hχ
  · intro G _ C _ V _ _ _ ρ z ω χ hω
    exact scalar_generalized_character_iff hω

end Langlands
