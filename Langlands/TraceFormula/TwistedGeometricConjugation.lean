import Langlands.BaseChange.TwistedOrbitalConjugation

/-! # Rational conjugation of a weighted twisted orbital term -/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure
open Langlands.QuotientIntegration Langlands.BaseChange

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (Γ : Subgroup G) (θ : G →* G) (δ x : G)

local notation "C₀" => twistedCentralizer θ δ
local notation "C₁" => twistedCentralizer θ (twistedConj θ x δ)
local notation "R₀" => Γ.subgroupOf (twistedCentralizer θ δ)
local notation "R₁" => Γ.subgroupOf (twistedCentralizer θ (twistedConj θ x δ))

private theorem twistedCentralizerConj_mem_rational (hx : x ∈ Γ) (y : C₀) :
    twistedCentralizerConj θ δ x y ∈ R₁ ↔ y ∈ R₀ := by
  change ((twistedCentralizerConj θ δ x y : C₁) : G) ∈ Γ ↔ (y : G) ∈ Γ
  rw [twistedCentralizerConj_apply_coe]
  constructor
  · intro h
    have e : x * (x⁻¹ * y.val * x) * x⁻¹ = y.val := by group
    exact e ▸ Γ.mul_mem (Γ.mul_mem hx h) (Γ.inv_mem hx)
  · intro h
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hx) h) hx

private def twistedRationalCentralizerConj (hx : x ∈ Γ) : R₀ ≃ₜ* R₁ :=
  subgroupContinuousMulEquiv (twistedCentralizerConj θ δ x) R₀ R₁
    (twistedCentralizerConj_mem_rational Γ θ δ x hx)

private def twistedRationalCentralizerQuotientConj (hx : x ∈ Γ) :
    LeftQuotient R₀ ≃ₜ LeftQuotient R₁ :=
  Homeomorph.Quotient.congr (twistedCentralizerConj θ δ x).toHomeomorph (by
    intro y z
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change z * y⁻¹ ∈ R₀ ↔
      twistedCentralizerConj θ δ x z * (twistedCentralizerConj θ δ x y)⁻¹ ∈ R₁
    rw [← map_inv, ← map_mul]
    exact (twistedCentralizerConj_mem_rational Γ θ δ x hx _).symm)

private theorem map_count_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) : Measure.map e (Measure.count : Measure X) = Measure.count := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, Measure.count_apply (e.measurable hs),
    Measure.count_apply hs, Set.encard_preimage_of_bijective e.bijective]

variable [MeasurableSpace G] [BorelSpace G]

/-- Conjugating by a rational-subgroup element transports both compatible
quotient measures and preserves the covolume and the orbital integral. -/
def TwistedGeometricConjugationStatement : Prop :=
  x ∈ Γ →
    ∀ (μG : Measure G) [μG.IsMulLeftInvariant] (μC : Measure C₀) [μC.IsMulRightInvariant]
      [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (ν : Measure (LeftQuotient C₀)) (νΓ : Measure (LeftQuotient R₀)),
      IsCompatible C₀ μG μC ν → IsCompatible R₀ μC Measure.count νΓ →
      ∃ (μC' : Measure C₁) (ν' : Measure (LeftQuotient C₁)) (νΓ' : Measure (LeftQuotient R₁)),
        IsFiniteMeasureOnCompacts μC' ∧ μC'.IsOpenPosMeasure ∧
        ∃ hR' : μC'.IsMulRightInvariant,
          letI := hR'
          IsCompatible C₁ μG μC' ν' ∧ IsCompatible R₁ μC' Measure.count νΓ' ∧
          νΓ' Set.univ = νΓ Set.univ ∧
          ∀ f : G → ℂ,
            twistedOrbitalIntegral θ (twistedConj θ x δ) ν' f = twistedOrbitalIntegral θ δ ν f

set_option maxHeartbeats 750000 in
theorem twistedGeometricConjugation : TwistedGeometricConjugationStatement Γ θ δ x := by
  intro hx μG _ μC _ _ _ ν νΓ hν hνΓ
  let eC := twistedCentralizerConj θ δ x
  let eQ := twistedOrbitQuotientConj θ δ x
  let eΓ := twistedRationalCentralizerConj Γ θ δ x hx
  let eΓQ := twistedRationalCentralizerQuotientConj Γ θ δ x hx
  let μC' := Measure.map eC μC
  let ν' := Measure.map eQ ν
  let νΓ' := Measure.map eΓQ νΓ
  let hR' : μC'.IsMulRightInvariant := isMulRightInvariant_map eC μC
  have hFin : IsFiniteMeasureOnCompacts μC' :=
    IsFiniteMeasureOnCompacts.map μC eC.toHomeomorph
  have hPos : μC'.IsOpenPosMeasure := eC.continuous.isOpenPosMeasure_map eC.surjective
  have hν' : IsCompatible C₁ μG μC' ν' :=
    isCompatible_map_twistedConj θ δ x μC μC' μG rfl ν hν
  have hνΓ' : IsCompatible R₁ μC' Measure.count νΓ' := by
    have hmap := isCompatible_map_equiv eC R₀ R₁ eΓ (fun _ => rfl) eΓQ (fun _ => rfl)
      μC Measure.count νΓ hνΓ
    have hcount : Measure.map eΓ (Measure.count : Measure R₀) = Measure.count :=
      map_count_eq eΓ.toHomeomorph.toMeasurableEquiv
    simpa only [hcount] using hmap
  refine ⟨μC', ν', νΓ', hFin, hPos, hR', hν', hνΓ', ?_, ?_⟩
  · rw [show νΓ' = Measure.map eΓQ νΓ from rfl,
      Measure.map_apply eΓQ.continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  · intro f
    exact (twistedOrbitalIntegral_map_conj θ δ x ν f).2

end Langlands.TraceFormula
