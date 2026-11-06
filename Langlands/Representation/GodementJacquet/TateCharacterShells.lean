import Langlands.Representation.RankinSelberg.ValuationShellIntegrationProof
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Langlands.HarmonicAnalysis.Conductor
import Langlands.Group.GL.UnramifiedCharacter

/-! Actual character averages and tails of scalar Mellin shell coefficients. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uG

section CharacterAverage

variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul G]
  (μ : Measure G) [μ.IsMulLeftInvariant]

/-- A nontrivial character averages to zero on a measurable subgroup.
No finiteness or integrability assumption is needed for this cancellation. -/
theorem integral_character_subgroup_eq_zero (K : Subgroup G)
    (hK : MeasurableSet (K : Set G)) (χ : G →* ℂ)
    (hχ : ∃ u ∈ K, χ u ≠ 1) :
    (∫ a in (K : Set G), χ a ∂μ) = 0 := by
  classical
  obtain ⟨u, hu, hχu⟩ := hχ
  have hmul (a : G) :
      (K : Set G).indicator (fun a => χ a) (u * a) =
        χ u * (K : Set G).indicator (fun a => χ a) a := by
    by_cases ha : a ∈ K
    · rw [Set.indicator_of_mem (K.mul_mem hu ha), Set.indicator_of_mem ha, map_mul]
    · rw [Set.indicator_of_notMem (fun hua => ha ((K.mul_mem_cancel_left hu).mp hua)),
        Set.indicator_of_notMem ha, mul_zero]
  have hI : χ u * (∫ a in (K : Set G), χ a ∂μ) =
      ∫ a in (K : Set G), χ a ∂μ := by
    rw [← integral_const_mul, ← integral_indicator hK, ← integral_indicator hK]
    calc
      (∫ a, (K : Set G).indicator (fun a => χ u * χ a) a ∂μ) =
          ∫ a, χ u * (K : Set G).indicator (fun a => χ a) a ∂μ := by
        congr 1
        funext a
        by_cases ha : a ∈ K <;> simp [ha]
      _ = ∫ a, (K : Set G).indicator (fun a => χ a) (u * a) ∂μ := by
        simp_rw [hmul]
      _ = _ := integral_mul_left_eq_self _ u
  have hz : (χ u - 1) * (∫ a in (K : Set G), χ a ∂μ) = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)

end CharacterAverage

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @Quasicharacter F.Carrier _ T.topology
local notation "TestFunction" => @SchwartzBruhat F.Carrier T.topology

/-- The actual integral-unit subgroup is precisely the order-zero shell. -/
theorem mem_integralUnits_iff_ord_zero (a : F.Carrierˣ) :
    letI := T.valuativeRel
    a ∈ RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer ↔
      T.ord (a : F.Carrier) = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  obtain ⟨π, hπ, hK, _⟩ := valuationShellIntegration p inferInstance F T
  exact (Set.ext_iff.mp hK a).symm

/-- Conductor zero is exactly triviality on the actual integral units. -/
theorem conductor_zero_iff_integralUnits (χ : MultiplicativeCharacter) :
    letI := T.valuativeRel
    T.multiplicativeConductor χ = 0 ↔
      ∀ a ∈ RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer,
        χ a = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  rw [T.multiplicativeConductor_eq_zero_iff]
  unfold PadicField.TopologicalData.IsUnramifiedQuasicharacter
  have hval (a : F.Carrierˣ) : T.discreteValuation (a : F.Carrier) = 1 ↔
      a ∈ RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer := by
    rw [mem_integralUnits_iff_ord_zero F T, T.ord_eq_zero_iff_normalizedAbs,
      T.normalizedAbs_eq_one_iff_discreteValuation]
  exact forall_congr' fun a => by rw [hval]

/-- Haar mass one on integral units gives the exact character average,
including the conductor-nonzero case. -/
theorem integral_character_integralUnits (χ : MultiplicativeCharacter) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    (∫ a in (RankinSelberg.integralUnits
      (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ),
      (χ a : ℂ) ∂localMultiplicativeHaar F.Carrier) =
        if T.multiplicativeConductor χ = 0 then 1 else 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  classical
  let K := RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer
  have hKm : MeasurableSet (K : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ (Valuation.isOpen_integer
      (v := ValuativeRel.valuation F.Carrier))).measurableSet
  by_cases hχ : T.multiplicativeConductor χ = 0
  · rw [ite_eq_left hχ]
    have htriv := (conductor_zero_iff_integralUnits F T χ).mp hχ
    calc
      (∫ a in (K : Set F.Carrierˣ), (χ a : ℂ) ∂localMultiplicativeHaar F.Carrier) =
          ∫ _a in (K : Set F.Carrierˣ), (1 : ℂ) ∂localMultiplicativeHaar F.Carrier := by
        exact setIntegral_congr_fun hKm fun a ha => by rw [htriv a ha]; rfl
      _ = 1 := by simp [K, measureReal_def]
  · rw [ite_eq_right hχ]
    refine integral_character_subgroup_eq_zero (localMultiplicativeHaar F.Carrier) K hKm
      ((Units.coeHom ℂ).comp χ.toMonoidHom) ?_
    have hn := mt (conductor_zero_iff_integralUnits F T χ).mpr hχ
    push Not at hn
    obtain ⟨u, hu, hχu⟩ := hn
    exact ⟨u, hu, fun h => hχu (Units.ext h)⟩

/-- Actual character-weighted scalar shell coefficient. -/
def characterShellCoefficient (χ : MultiplicativeCharacter) (π : F.Carrierˣ)
    (Φ : TestFunction) (n : ℤ) : ℂ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  exact ∫ u in (RankinSelberg.integralUnits
      (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ),
    Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) * (χ (π ^ n * u) : ℂ)
      ∂localMultiplicativeHaar F.Carrier

/-- Every test has the exact geometric character tail if unramified,
and an identically zero tail otherwise. -/
theorem characterShellCoefficient_eventual (χ : MultiplicativeCharacter)
    (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (Φ : TestFunction) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n →
      characterShellCoefficient F T χ π Φ n =
        if T.multiplicativeConductor χ = 0 then Φ 0 * (χ π : ℂ) ^ n else 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  classical
  obtain ⟨L, N, C, hLN, hC, hbound, hlow, hhigh⟩ :=
    schwartzBruhatValuationBounds p F T Φ
  refine ⟨N, fun n hn => ?_⟩
  let K := RankinSelberg.integralUnits (ValuativeRel.valuation F.Carrier).integer
  have hKm : MeasurableSet (K : Set F.Carrierˣ) :=
    (integralUnits_isOpen _ (Valuation.isOpen_integer
      (v := ValuativeRel.valuation F.Carrier))).measurableSet
  have hord (u : F.Carrierˣ) (hu : u ∈ K) :
      T.ord ((π ^ n * u : F.Carrierˣ) : F.Carrier) = n := by
    rw [Units.val_mul, T.ord_mul (Units.ne_zero _) u.ne_zero,
      Units.val_zpow_eq_zpow_val, T.ord_zpow, hπ, mul_one,
      (mem_integralUnits_iff_ord_zero F T u).mp hu, add_zero]
  calc
    characterShellCoefficient F T χ π Φ n =
        (Φ 0 * (χ π : ℂ) ^ n) *
          (∫ u in (K : Set F.Carrierˣ), (χ u : ℂ)
            ∂localMultiplicativeHaar F.Carrier) := by
      unfold characterShellCoefficient
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hKm fun u hu => ?_
      rw [hhigh _ (by rw [hord u hu]; exact hn), map_mul, map_zpow]
      simp [mul_assoc]
    _ = _ := by
      rw [integral_character_integralUnits F T χ]
      split_ifs <;> simp

end Padic

end Langlands.GodementJacquet
