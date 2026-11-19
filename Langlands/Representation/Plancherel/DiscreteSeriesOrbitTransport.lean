import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDiscreteSeriesOrbitFiniteness
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure

/-! # Actual discrete-series orbit measures under group and character equivalences -/

noncomputable section

universe uG uH uV uI uJ

open MeasureTheory Langlands.HarishChandraSchwartz
open scoped NNReal ENNReal

namespace Langlands.Plancherel

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  (e : H ≃ₜ* G)
  {I : Type uI} {J : Type uJ}
  (νG : I → (G →* ℝ≥0ˣ)) (νH : J → (H →* ℝ≥0ˣ))
  (eX : unitaryUnramifiedCharacters νG ≃ₜ* unitaryUnramifiedCharacters νH)
  (hX : ∀ (χ : unitaryUnramifiedCharacters νG) (h : H), (eX χ).val h = χ.val (e h))
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
  (hAB : B.map e.toMonoidHom = A)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
  (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure]
  (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure]
  (hμ : Measure.map (quotientContinuousMulEquiv e A B hAB) μH = μG)

include hX in
/-- Pullback commutes with the displayed actual character equivalence even
when the two norm families have different index types. -/
theorem discreteSeriesPullback_smul_characterEquiv
    (χ : unitaryUnramifiedCharacters νG) (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ (χ • ω) =
      eX χ • DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ ω := by
  have hχ : χ.val.toMonoidHom.comp e.toMonoidHom = (eX χ).val.toMonoidHom :=
    MonoidHom.ext (fun h => (hX χ h).symm)
  apply Subtype.ext
  change SmoothDualClass.pullback e (SmoothDualClass.twist χ.val.toMonoidHom _ ω.val) =
    SmoothDualClass.twist (eX χ).val.toMonoidHom _ (SmoothDualClass.pullback e ω.val)
  rw [SmoothDualClass.pullback_twist e _ _
    ((unramifiedCharacter_isOpen_ker νG ⟨χ.val, χ.property.1⟩).preimage e.continuous)]
  simp only [hχ]

variable (ω : DiscreteSeriesClass.{uG, uV} A hA μG)

set_option hygiene false in
local notation "ωH" => DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ ω
set_option hygiene false in
local notation "SG" => discreteSeriesStabilizer A hA μG νG ω
set_option hygiene false in
local notation "SH" => discreteSeriesStabilizer B hB μH νH ωH

include hX in
/-- The actual self-twist stabilizers correspond under character transport. -/
theorem discreteSeriesStabilizer_map_characterEquiv :
    (SG).map eX.toMonoidHom = SH := by
  have heq := discreteSeriesPullback_smul_characterEquiv e νG νH eX hX
    A hA B hB hAB μG μH hμ
  have hinj := DiscreteSeriesClass.pullback_injective e A hA B hB hAB μG μH hμ
  ext χ
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    change eX ψ • ωH = ωH
    rw [← heq]
    exact congrArg (DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ) hψ
  · intro hχ
    refine ⟨eX.symm χ, ?_, eX.apply_symm_apply χ⟩
    change eX.symm χ • ω = ω
    apply hinj
    rw [heq, eX.apply_symm_apply]
    exact hχ

include hX in
/-- In particular, the self-twist factors in the orbit measures are equal. -/
theorem discreteSeriesStabilizer_card_characterEquiv :
    Nat.card SG = Nat.card SH := by
  let E := ((SG).equivMapOfInjective eX.toMonoidHom eX.injective).trans
    (MulEquiv.subgroupCongr
      (discreteSeriesStabilizer_map_characterEquiv e νG νH eX hX A hA B hB hAB μG μH hμ ω))
  exact Nat.card_congr E.toEquiv

/-- Transport of actual twist orbits through their actual self-twist
quotients. No topology on the entire smooth dual is used. -/
def discreteSeriesOrbitCharacterEquiv :
    discreteSeriesOrbit A hA μG νG ω ≃ₜ discreteSeriesOrbit B hB μH νH ωH :=
  (discreteSeriesOrbitHomeomorph A hA μG νG ω).symm.trans
    ((quotientContinuousMulEquiv eX SH SG
      (discreteSeriesStabilizer_map_characterEquiv e νG νH eX hX
        A hA B hB hAB μG μH hμ ω)).toHomeomorph.trans
      (discreteSeriesOrbitHomeomorph B hB μH νH ωH))

@[simp]
theorem discreteSeriesOrbitCharacterEquiv_orbitMap (χ : unitaryUnramifiedCharacters νG) :
    discreteSeriesOrbitCharacterEquiv e νG νH eX hX A hA B hB hAB μG μH hμ ω
      (discreteSeriesOrbitMap A hA μG νG ω χ) =
        discreteSeriesOrbitMap B hB μH νH ωH (eX χ) := by
  simp only [discreteSeriesOrbitCharacterEquiv, discreteSeriesOrbitMap,
    Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  rfl

variable [Finite SG] [Finite SH]

/-- The full orbit measure transports with the character measure. Both actual
self-twist cardinalities are kept and matched, with no probability replacement. -/
theorem map_discreteSeriesOrbitMeasure_characterEquiv
    (lambda : Measure (unitaryUnramifiedCharacters νG)) :
    Measure.map
        (discreteSeriesOrbitCharacterEquiv e νG νH eX hX A hA B hB hAB μG μH hμ ω)
        (discreteSeriesOrbitMeasure νG A hA μG ω lambda) =
      discreteSeriesOrbitMeasure νH B hB μH ωH (Measure.map eX lambda) := by
  let E := discreteSeriesOrbitCharacterEquiv e νG νH eX hX A hA B hB hAB μG μH hμ ω
  ext D hD
  rw [Measure.map_apply (f := fun x => E x) E.continuous.measurable hD,
    discreteSeriesOrbitMeasure_apply _ _ _ _ _ _ (E.continuous.measurable hD),
    discreteSeriesOrbitMeasure_apply _ _ _ _ _ _ hD,
    Measure.map_apply (f := fun χ => eX χ) eX.continuous.measurable
      ((continuous_discreteSeriesOrbitMap B hB μH νH ωH).measurable hD),
    discreteSeriesStabilizer_card_characterEquiv e νG νH eX hX A hA B hB hAB μG μH hμ ω]
  congr 2
  ext χ
  simp only [Set.mem_preimage, E, discreteSeriesOrbitCharacterEquiv_orbitMap]

end Langlands.Plancherel
