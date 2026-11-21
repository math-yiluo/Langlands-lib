import Langlands.Representation.Conductor.RankOneCharacterLevel
import Langlands.Representation.GodementJacquet.LocalTateUnits
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction

/-!
# Rank-one fixed levels and the multiplicative conductor

The Library's two definitions of rank-one conductors use the same
principal-unit filtration under the determinant.
-/

noncomputable section

namespace Langlands.Conductor

open GeneralLinear RankinSelberg HarmonicAnalysis
open GodementJacquet.LocalTate
open scoped WithZero

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private def tateNormalization (ϖ : Fˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ) : Normalization F where
  q := (LocalFieldData.ofInstances F).residueCardinality
  hq := rfl
  abv := AllField.RankinSelberg.normalizedAbsoluteValue (LocalFieldData.ofInstances F)
  ϖ := ϖ
  hϖ := hϖ
  habvϖ := by
    rw [AllField.RankinSelberg.normalizedAbsoluteValue_apply,
      (LocalFieldData.ofInstances F).normalizedAbs_of_ne_zero ϖ.ne_zero,
      AllField.RankinSelberg.ord_of_isUniformizingElement hϖ, zpow_neg_one]
  habv1 x hx := by
    have hdv : (LocalFieldData.ofInstances F).discreteValuation x = 1 := by
      rw [AllField.RankinSelberg.discreteValuation_ofInstances, hx, map_one]
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx
      exact zero_ne_one hx
    rw [AllField.RankinSelberg.normalizedAbsoluteValue_apply,
      (LocalFieldData.ofInstances F).normalizedAbs_of_ne_zero hx0, LocalFieldData.ord, hdv]
    simp

private theorem unitLevel_eq_principalUnits (N : Normalization F) (n : ℕ) :
    N.unitLevel n = (LocalFieldData.ofInstances F).principalUnits n := by
  let T := LocalFieldData.ofInstances F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  ext u
  rw [N.mem_unitLevel, N.mem_ball, T.mem_principalUnits,
    AllField.RankinSelberg.discreteValuation_ofInstances,
    AllField.RankinSelberg.discreteValuation_ofInstances]
  have hϖ : e (ValuativeRel.valuation F (N.ϖ : F)) = WithZero.exp (-1) :=
    AllField.RankinSelberg.discreteValuation_of_isUniformizingElement N.hϖ
  have hp : e (ValuativeRel.valuation F (N.ϖ : F) ^ (n : ℤ)) = WithZero.exp (-(n : ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    simp
  change _ ↔ e (ValuativeRel.valuation F (u : F)) = 1 ∧
    e (ValuativeRel.valuation F ((u : F) - 1)) ≤ WithZero.exp (-(n : ℤ))
  rw [← hp, e.strictMono.le_iff_le, ← map_one e]
  exact and_congr ⟨congrArg e, fun h => e.injective h⟩ Iff.rfl

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (GeneralLinear 1 F) V}

/-- The multiplicative conductor is a finite newvector conductor for any
actual model of a rank-one quasicharacter. -/
theorem isNewvectorConductor_of_multiplicativeConductor (χ : Quasicharacter F)
    (e : ρ.Equiv (rankOneCharacter χ.toMonoidHom)) :
    IsNewvectorConductor ρ ((LocalFieldData.ofInstances F).multiplicativeConductor χ) := by
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F
  let N := tateNormalization ϖ hϖ
  let T := LocalFieldData.ofInstances F
  let a := T.multiplicativeConductor χ
  refine isNewvectorConductor_of_character e a ((N.level_trivial_iff _ a).mpr ?_) ?_
  · rw [unitLevel_eq_principalUnits N a]
    exact T.multiplicativeConductor_spec χ
  · intro b hb
    obtain ⟨u, hu, hχ⟩ := T.exists_nontrivial_below_multiplicativeConductor χ b hb
    have hu' : u ∈ N.unitLevel b := (unitLevel_eq_principalUnits N b).symm ▸ hu
    obtain ⟨g, hg, hdet⟩ := N.exists_determinant_eq hu'
    exact ⟨g, hg, hdet ▸ hχ⟩

/-- The total first fixed level of an actual rank-one character model is its
finite multiplicative conductor. -/
theorem firstFixedLevel_eq_multiplicativeConductor (χ : Quasicharacter F)
    (e : ρ.Equiv (rankOneCharacter χ.toMonoidHom)) :
    firstFixedLevel ρ = ((LocalFieldData.ofInstances F).multiplicativeConductor χ : WithTop ℕ) := by
  have ha := isNewvectorConductor_of_multiplicativeConductor χ e
  have h : HasNewvectorLevel ρ := ⟨_, ha.1⟩
  rw [firstFixedLevel_of_hasNewvectorLevel ρ h, (newvectorConductor_eq_iff ρ h _).mpr ha]

end Langlands.Conductor
