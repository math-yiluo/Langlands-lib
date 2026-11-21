import Langlands.JacquetLanglands.LocalCharacter
import Langlands.Representation.Character.ModularConjugationProof

noncomputable section

namespace Langlands.JacquetLanglands

open MeasureTheory HarmonicAnalysis

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A local character value is invariant under conjugation. The character distribution and
Haar integration have the same modular transformation, so the value needs no factor. -/
theorem HasCharacterValue.conjugate {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}
    {g : G} {c : ℂ} (h : HasCharacterValue ρ hρ g c) (a : G) :
    HasCharacterValue ρ hρ (a⁻¹ * g * a) c := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hU, hg, hval⟩ := h μ
  let e := Distribution.conjugationHomeomorph a
  refine ⟨e ⁻¹' U, hU.preimage e.continuous, ?_, ?_⟩
  · change a * (a⁻¹ * g * a) * a⁻¹ ∈ U
    simpa [mul_assoc] using hg
  · intro f hf
    let k := Hecke.TestFunction.pullback (Distribution.conjugationHomeomorph a⁻¹) f
    have hk : Function.support k ⊆ U := by
      intro x hx
      have hs : a⁻¹ * x * a ∈ Function.support (f : G → ℂ) := by
        simpa [Function.mem_support, k] using hx
      have hx' := hf hs
      change a * (a⁻¹ * x * a) * a⁻¹ ∈ U at hx'
      simpa [mul_assoc] using hx'
    have hd := Character.distribution_conjugation_modular μ ρ hρ a⁻¹ f
    have hi := (Distribution.RenardModular.translation G μ).2 f a⁻¹ a⁻¹
    have hmod : ((Distribution.renardModular a⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have hpos := (Distribution.RenardModular.regularity G).1 a⁻¹
      exact Complex.ofReal_ne_zero.mpr (by exact_mod_cast hpos.ne')
    change Character.distribution μ ρ hρ k = _ at hd
    change (∫ x, k x ∂μ) = _ at hi
    have hv := hval k hk
    rw [hd, hi, Distribution.ofMeasure_apply, mul_left_comm c] at hv
    exact mul_left_cancel₀ hmod hv

end Langlands.JacquetLanglands
