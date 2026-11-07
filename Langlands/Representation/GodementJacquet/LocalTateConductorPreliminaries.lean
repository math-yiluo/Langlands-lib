import Langlands.Representation.GodementJacquet.LocalTateConductorStatement
import Langlands.Representation.Conductor.RankOne
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof

/-! Natural rank-one conductors and actual scalar Fourier witnesses. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis GeneralLinear Conductor Topology

universe uF

section Conductor

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- A continuous field character is trivial at some actual rank-one level. -/
theorem exists_character_level (χ : Fˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ a : ℕ, ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1 := by
  let O : Set (Langlands.GeneralLinear 1 F) :=
    {g | ‖(χ (determinant g) : ℂ) - 1‖ < (1 / 2 : ℝ)}
  have hdet : Continuous (determinant : Langlands.GeneralLinear 1 F → Fˣ) :=
    Matrix.GeneralLinearGroup.continuous_det
  have hO : IsOpen O :=
    isOpen_lt ((Units.continuous_val.comp (hχ.comp hdet)).sub continuous_const).norm
      continuous_const
  have h1 : (1 : Langlands.GeneralLinear 1 F) ∈ O := by simp [O]
  obtain ⟨a, ha⟩ := rankOne_level_cofinal F (hO.mem_nhds h1)
  refine ⟨a, fun g hg => Units.ext ?_⟩
  change (χ (determinant g) : ℂ) = 1
  apply Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt
  intro n
  have hn := ha ((levelSubgroup F 0 a).pow_mem hg n)
  simpa [O] using hn

/-- A unique natural exponent is trivial at its level and nontrivial at every
smaller actual rank-one level. No conductor input is assumed. -/
theorem existsUnique_character_conductor (χ : Fˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃! a : ℕ,
      (∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) ∧
      (∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1) := by
  classical
  let h := exists_character_level F χ hχ
  refine ⟨Nat.find h, ⟨Nat.find_spec h, ?_⟩, ?_⟩
  · intro b hb
    have hn := Nat.find_min h hb
    push Not at hn
    exact hn
  · intro a ha
    apply le_antisymm
    · by_contra hn
      obtain ⟨g, hg, hχg⟩ := ha.2 (Nat.find h) (by omega)
      exact hχg (Nat.find_spec h g hg)
    · exact Nat.find_min' h ha.1

/-- The natural conductor constructed from character continuity and the
actual rank-one level filtration. -/
def characterConductor (χ : Fˣ →* ℂˣ) (hχ : Continuous χ) : ℕ :=
  (existsUnique_character_conductor F χ hχ).exists.choose

/-- The constructed conductor satisfies both exact level conditions. -/
theorem characterConductor_spec (χ : Fˣ →* ℂˣ) (hχ : Continuous χ) :
    (∀ g ∈ levelSubgroup F 0 (characterConductor F χ hχ), χ (determinant g) = 1) ∧
      (∀ b < characterConductor F χ hχ,
        ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1) :=
  (existsUnique_character_conductor F χ hχ).exists.choose_spec

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Inversion preserves the exact character-level conductor characterization. -/
theorem character_conductor_inv_iff (χ : Fˣ →* ℂˣ) (a : ℕ) :
    ((∀ g ∈ levelSubgroup F 0 a, (χ (determinant g))⁻¹ = 1) ∧
      (∀ b < a, ∃ g ∈ levelSubgroup F 0 b, (χ (determinant g))⁻¹ ≠ 1)) ↔
    ((∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) ∧
      (∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1)) := by
  simp only [inv_eq_one, inv_ne_one]

end Conductor

section Fourier

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F] [T2Space F]
  [TotallyDisconnectedSpace F]

/-- The supplied self-dual measure gives an integrable plus-sign Fourier
transform in the actual Schwartz--Bruhat space. -/
theorem exists_scalar_fourier_witness (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F) (hν : IsSelfDual ψ ν) (Φ : SchwartzBruhat F) :
    ∃ Φhat : SchwartzBruhat F, ∀ y,
      Integrable (fun x => ψ.complex (x * y) * Φ x) ν.measure ∧
      Φhat y = fourierIntegral ψ ν Φ y := by
  obtain ⟨Φhat, hΦhat⟩ := (scalarFourierClosure F ψ ν hν).2 Φ
  exact ⟨Φhat, fun y => ⟨fourierIntegrand_integrable ψ ν Φ y, hΦhat y⟩⟩

end Fourier

end Langlands.GodementJacquet
