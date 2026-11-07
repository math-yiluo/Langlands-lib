import Langlands.Representation.Conductor.RankOne
import Langlands.Representation.GodementJacquet.LocalTateEpsilonTransport

/-! Character-level criteria on the actual rank-one representation carrier. -/

noncomputable section

namespace Langlands.Conductor

open GeneralLinear RankinSelberg GodementJacquet Whittaker HarmonicAnalysis MeasureTheory

universe uF uV

section Levels

variable {F : Type uF} [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (Langlands.GeneralLinear 1 F) V} {χ : Fˣ →* ℂˣ}
  (φ : π.Equiv (rankOneCharacter χ))

include φ

omit [ValuativeRel F] in
/-- The actual character coordinates intertwine the given action. -/
theorem rankOneCharacterEquiv_apply (g : Langlands.GeneralLinear 1 F) (v : V) :
    φ (π g v) = (χ (determinant g) : ℂ) * φ v := by
  exact LinearMap.congr_fun (φ.isIntertwining' g) v

/-- If the character is trivial at a level, the whole actual carrier is fixed. -/
theorem levelFixedVectors_eq_top_of_character (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) :
    levelFixedVectors π a = ⊤ := by
  apply top_unique
  intro v _
  apply (mem_levelFixedVectors π a v).2
  intro g hg
  apply φ.toLinearEquiv.injective
  change φ (π g v) = φ v
  rw [rankOneCharacterEquiv_apply φ, ha g hg, Units.val_one, one_mul]

/-- Character coordinates restrict to an equivalence on the actual fixed space
at every level where the character is trivial. -/
def rankOneCharacterLevelEquiv (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) :
    levelFixedVectors π a ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.ofTop _ (levelFixedVectors_eq_top_of_character φ a ha)).trans
    φ.toLinearEquiv

/-- Such a fixed space is a line, with no dimension premise. -/
theorem finrank_levelFixedVectors_of_character (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1) :
    Module.finrank ℂ (levelFixedVectors π a) = 1 := by
  rw [(rankOneCharacterLevelEquiv φ a ha).finrank_eq]
  exact Module.finrank_self ℂ

/-- A single nontrivial character value at a level forces its fixed space to vanish. -/
theorem levelFixedVectors_eq_bot_of_character (a : ℕ)
    (ha : ∃ g ∈ levelSubgroup F 0 a, χ (determinant g) ≠ 1) :
    levelFixedVectors π a = ⊥ := by
  obtain ⟨g, hg, hχg⟩ := ha
  apply bot_unique
  intro v hv
  change v = 0
  have hfix := (mem_levelFixedVectors π a v).1 hv g hg
  have hmul : (χ (determinant g) : ℂ) * φ v = φ v := by
    rw [← rankOneCharacterEquiv_apply φ, hfix]
  have hχne : (χ (determinant g) : ℂ) ≠ 1 := fun h => hχg (Units.ext h)
  have hz : ((χ (determinant g) : ℂ) - 1) * φ v = 0 := by
    linear_combination hmul
  have hvzero := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχne)
  apply φ.toLinearEquiv.injective
  change φ v = φ 0
  simpa only [map_zero] using hvzero

/-- The least principal-unit conductor is the actual least nonzero fixed level
of every representation equivalent to the character. -/
theorem isNewvectorConductor_of_character (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1)
    (hmin : ∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1) :
    IsNewvectorConductor π a := by
  refine ⟨?_, fun b hb => levelFixedVectors_eq_bot_of_character φ b (hmin b hb)⟩
  have hw : φ.symm 1 ∈ levelFixedVectors π a := by
    rw [levelFixedVectors_eq_top_of_character φ a ha]
    trivial
  intro hbot
  rw [hbot] at hw
  have hz : φ.symm 1 = 0 := hw
  have h := congrArg φ hz
  exact one_ne_zero (by
    simpa only [Representation.Equiv.apply_symm_apply, map_zero] using h)

end Levels

section Conductor

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
  (hπ : IsSmooth π) {χ : Fˣ →* ℂˣ} (φ : π.Equiv (rankOneCharacter χ))

include φ

/-- The smoothness-constructed conductor equals the character's least level. -/
theorem rankOneConductor_eq_of_character (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1)
    (hmin : ∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1) :
    rankOneConductor F π hπ = a :=
  (newvectorConductor_spec π (hasNewvectorLevel_rankOne F π hπ)).unique
    (isNewvectorConductor_of_character φ a ha hmin)

end Conductor

section Epsilon

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
  (χ : Fˣ →* ℂˣ) (φ : π.Equiv (rankOneCharacter χ))

include φ

/-- Supplied scalar Tate data at the least character level yield the rank-one
conductor conclusions on the original carrier, with the same epsilon coefficient. -/
theorem rankOneConductorConclusion_of_scalar (a : ℕ)
    (ha : ∀ g ∈ levelSubgroup F 0 a, χ (determinant g) = 1)
    (hmin : ∀ b < a, ∃ g ∈ levelSubgroup F 0 b, χ (determinant g) ≠ 1)
    (c : ℂˣ)
    (h : ScalarTateEpsilonData q ψ abv (localMultiplicativeHaar F) ν χ c (a : ℤ)) :
    IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter 1) (c, (a : ℤ)) ∧
    IsNewvectorConductor π a ∧ Module.finrank ℂ (levelFixedVectors π a) = 1 := by
  refine ⟨?_, isNewvectorConductor_of_character φ a ha hmin,
    finrank_levelFixedVectors_of_character φ a ha⟩
  exact (tateIsPairEpsilonFactor_of_scalar F q ψ abv ν χ c (a : ℤ) h).of_equiv
    φ.symm (Representation.Equiv.refl _)

end Epsilon

end Langlands.Conductor
