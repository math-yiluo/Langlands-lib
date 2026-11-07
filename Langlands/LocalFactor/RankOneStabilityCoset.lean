import Langlands.LocalFactor.RankOneStabilityStatement
import Langlands.LocalFactor.Abelian.GaussDual
import Langlands.HarmonicAnalysis.CharacterSeparation

/-! Bounded-conductor character separation and the full twist-witness coset. -/

noncomputable section

open MeasureTheory Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- Characters of conductor at most `k` detect precisely the quotient by `U^k`.
The field, supplied topology and carrier universe are arbitrary. -/
theorem mem_principalUnits_iff_bounded_characters (k : ℕ) (v : F.Carrierˣ) :
    v ∈ T.principalUnits k ↔
      ∀ η : Character, T.multiplicativeConductor η ≤ k → η v = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  constructor
  · intro hv η hη
    exact (T.multiplicativeTrivialAt_iff_conductor_le η k).mpr hη v hv
  · intro hv
    by_contra hnot
    let H := T.principalUnits k
    let : DiscreteTopology (F.Carrierˣ ⧸ H) :=
      QuotientGroup.discreteTopology (HarmonicAnalysis.CharacterSeparation.principalUnits_isOpen T k)
    have hq : (QuotientGroup.mk' H) v ≠ 1 := by
      intro h
      exact hnot ((QuotientGroup.eq_one_iff v).mp h)
    obtain ⟨c, hc⟩ := HarmonicAnalysis.CharacterSeparation.exists_discrete_character ((QuotientGroup.mk' H) v) hq
    let q : F.Carrierˣ →ₜ* F.Carrierˣ ⧸ H :=
      { QuotientGroup.mk' H with continuous_toFun := QuotientGroup.continuous_mk }
    let η : Character := c.comp q
    have hη : T.multiplicativeConductor η ≤ k := by
      apply (T.multiplicativeTrivialAt_iff_conductor_le η k).mp
      intro w hw
      change c ((QuotientGroup.mk' H) w) = 1
      have heq : (QuotientGroup.mk' H) w = 1 :=
        (QuotientGroup.eq_one_iff w).mpr hw
      rw [heq, map_one]
    exact hc (hv η hη)

/-- Nonvanishing for the actual epsilon constructor at every supplied Haar measure. -/
theorem epsilon_ne_zero (χ : Character) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : ℂ) :
    letI := T.topology
    letI := borel F.Carrier
    epsilon T χ ψ μ.measure s ≠ 0 := by
  let := T.topology
  let := borel F.Carrier
  exact epsilonAt_ne_zero T (uniformizerUnit T) χ
    ((conductorAt_iff T χ _).mpr rfl) ψ (T.additiveConductor ψ) μ
    ((additiveConductorAt_iff T ψ _).mpr rfl) s

/-- Relative to any one twist witness, all witnesses form the exact `U^floor(a/2)`
coset. This lemma proves uniqueness; it does not assume witness existence in the
unconditional rank-one stability target. -/
theorem rankOneTwistWitness_iff_mem_coset (χ : Character) (ψ : AdditiveCharacter)
    (γ : F.Carrierˣ) (hγ : RankOneTwistWitness T χ ψ γ) (γ' : F.Carrierˣ) :
    RankOneTwistWitness T χ ψ γ' ↔
      γ' * γ⁻¹ ∈ T.principalUnits (T.multiplicativeConductor χ / 2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  constructor
  · intro hγ'
    apply (mem_principalUnits_iff_bounded_characters T _ _).mpr
    intro η hη
    have hb : 2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ := by
      omega
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts F.Carrier) := inferInstance
    let μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier :=
      HarmonicAnalysis.normalizedAdditiveHaar F.Carrier K
    have he : (η γ' : ℂ) * epsilon T χ ψ μ.measure 0 =
        (η γ : ℂ) * epsilon T χ ψ μ.measure 0 :=
      (hγ' η hb μ 0).symm.trans (hγ η hb μ 0)
    have hval : (η γ' : ℂ) = (η γ : ℂ) :=
      mul_right_cancel₀ (epsilon_ne_zero T χ ψ μ 0) he
    have hu : η γ' = η γ := Units.ext hval
    simp only [map_mul, map_inv, hu, mul_inv_cancel]
  · intro hcos η hη μ s
    have hk : T.multiplicativeConductor η ≤ T.multiplicativeConductor χ / 2 := by
      omega
    have hval : η (γ' * γ⁻¹) = 1 :=
      (mem_principalUnits_iff_bounded_characters T _ _).mp hcos η hk
    have hu : η γ' = η γ := by
      apply mul_inv_eq_one.mp
      simpa only [map_mul, map_inv] using hval
    simpa only [hu] using hγ η hη μ s

/-- An actual continuous quasicharacter with a certified conductor bound
that detects any element outside the specified principal-unit subgroup. -/
def separatingQuasicharacter (k : ℕ) (v : F.Carrierˣ)
    (hv : v ∉ T.principalUnits k) :
    {η : Character // T.multiplicativeConductor η ≤ k ∧ η v ≠ 1} := by
  classical
  have hex : ∃ η : Character, T.multiplicativeConductor η ≤ k ∧ η v ≠ 1 := by
    by_contra h
    push Not at h
    exact hv ((mem_principalUnits_iff_bounded_characters T k v).mpr h)
  exact ⟨hex.choose, hex.choose_spec⟩

end Langlands.LocalFactor.PadicAbelian
