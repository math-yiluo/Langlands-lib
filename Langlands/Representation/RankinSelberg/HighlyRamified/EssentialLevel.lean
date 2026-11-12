import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialDualIntegral
import Langlands.Representation.RankinSelberg.HighlyRamified.UnitarySeparation
import Langlands.Representation.RankinSelberg.HighlyRamified.ZeroCellLift

/-!
# The level of the zero-cell Kirillov lift

Let `π` be a generic representation of `GL_(n+3)(F)` such that, for every norm-one tuple
`z`, the gamma factor of `(π, I(z))` is `c^(n+2) (∏ z_i)^m X^((n+2) m)`. Then the zero-cell
Kirillov lift `w` of `π` is fixed by `K_1(m)`.

The forward integral of `w` against `W(·; z; ψ̄)` is `1`. The forward integral of the
dual-translated zero-cell vector `Y` of `π^ι` is a nonzero constant `C₀`
(`forward_corankOne_dualTranslate_eq`). So `w - C₀⁻¹ Y` has vanishing integrals for all
norm-one `z`, hence vanishes on the mirabolic subgroup (`UnitarySeparation`) and is zero
by Kirillov injectivity. Then the dual of `w` is `C₀⁻¹` times the translate of a zero-cell
vector by `diag(ϖ^m I_(n+2), 1)`, and the Library's form of JPSS (5.3) puts `w` at level `m`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance essentialLevelFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance essentialLevelValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance essentialLevelLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance essentialLevelFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance essentialLevelFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance essentialLevelGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance essentialLevelGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance essentialLevelUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance essentialLevelUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance essentialLevelQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance essentialLevelQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "ϖF" => F.canonicalTopologicalData.uniformizerUnit

/-- The canonical uniformizer has normalized absolute value `q⁻¹`. -/
theorem abv_uniformizerUnit : abv (ϖF : F.Carrier) = (qF : ℝ)⁻¹ := by
  have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs F.canonicalTopologicalData 1
  rw [zpow_one, zpow_neg_one] at h
  rw [normalizedAbsoluteValue_apply]
  exact h

/-- The Whittaker function of `π^ι(d) v'` is `x ↦ W'(w₀ ᵗx⁻¹ d)`, where `W'` is the
Whittaker function of `v'` for `π^ι` and the first dual functional. -/
theorem coefficient_dualTranslate_apply (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n π) (v' : V) (d x : GeneralLinear (n + 1) F.Carrier) :
    (coefficientMap π ℓ (inverseTransposePullback π d v')).val x =
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val
        (weylLong (n + 1) F.Carrier * inverseTranspose (n + 1) F.Carrier x * d) := by
  have h := congrArg
    (fun f : WhittakerFunctions (ψ.scale (-1)) n =>
      f.val (weylLong (n + 1) F.Carrier * inverseTranspose (n + 1) F.Carrier x))
    (firstDualFunction_coefficient ψ π ℓ (inverseTransposePullback π d v'))
  simp only [firstDualFunction_apply, weylLong_inverseTranspose_involutive] at h
  rw [h]
  change (firstDualFunctional ψ π ℓ).val (inverseTransposePullback π
      (weylLong (n + 1) F.Carrier * inverseTranspose (n + 1) F.Carrier x)
      (inverseTransposePullback π d v')) =
    (firstDualFunctional ψ π ℓ).val (inverseTransposePullback π
      (weylLong (n + 1) F.Carrier * inverseTranspose (n + 1) F.Carrier x * d) v')
  rw [map_mul (inverseTransposePullback π) _ d, Module.End.mul_apply]

/-- If the Whittaker function of `v'` for `π^ι` agrees with the zero-cell function on the
mirabolic subgroup, then the Whittaker function of `π^ι(d) v'`, for
`d = diag(ϖ^m I_(n+2), 1)`, is right invariant under `diag(GL_(n+2)(O), 1)` on
`diag(GL_(n+2), 1)`. -/
theorem dualTranslate_restriction_invariant (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : Conductor.HasIntegerConductor ψ) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ (n + 2) π)
    (hinj'' : Conductor.IsMirabolicRestrictionInjective (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ))
    (u : F.Carrierˣ) (v' : V)
    (hv' : ∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
      (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val g =
        (zeroCellWhittaker (Unramified.uniformizerUnit_isUniformizingElement F)
          (Conductor.hasIntegerConductor_scale_neg_one hψ).1 (n + 2)).val g)
    (g : GeneralLinear (n + 2) F.Carrier)
    (k : Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (n + 1)) :
    (coefficientMap π ℓ (inverseTransposePullback π
        (rankInclusion 1 (scalar (n := n + 2) u)) v')).val (rankInclusion 1 (g * k.val)) =
      (coefficientMap π ℓ (inverseTransposePullback π
        (rankInclusion 1 (scalar (n := n + 2) u)) v')).val (rankInclusion 1 g) := by
  rw [coefficient_dualTranslate_apply, coefficient_dualTranslate_apply]
  set d : GeneralLinear (n + 2 + 1) F.Carrier := rankInclusion 1 (scalar (n := n + 2) u)
    with hd
  set B : GeneralLinear (n + 2 + 1) F.Carrier :=
    rankInclusion 1 (inverseTranspose (n + 1 + 1) F.Carrier k.val) with hB
  have hcomm : B * d = d * B := by
    rw [hB, hd, ← map_mul, ← map_mul]
    congr 1
    exact (scalar_commute u _).symm
  have hBmem : B ∈ Conductor.fieldJacquetMirabolic (ValuativeRel.valuation F.Carrier).integer
      (n + 2) :=
    ⟨rankInclusion_mem_integralSubgroup (inverseTranspose_mem_integralSubgroup F k.property),
      rankInclusion_lastRow _⟩
  have hsplit : inverseTranspose (n + 2 + 1) F.Carrier (rankInclusion 1 (g * k.val)) =
      inverseTranspose (n + 2 + 1) F.Carrier (rankInclusion 1 g) * B := by
    rw [map_mul, map_mul, hB]
    congr 1
    exact inverseTranspose_rankInclusion _
  have key : weylLong (n + 2 + 1) F.Carrier *
        inverseTranspose (n + 2 + 1) F.Carrier (rankInclusion 1 (g * k.val)) * d =
      weylLong (n + 2 + 1) F.Carrier *
        inverseTranspose (n + 2 + 1) F.Carrier (rankInclusion 1 g) * d * B := by
    rw [hsplit]
    simp only [mul_assoc, hcomm]
  rw [key]
  exact zeroCell_mul_fieldJacquetMirabolic (Unramified.uniformizerUnit_isUniformizingElement F)
    (Conductor.hasIntegerConductor_scale_neg_one hψ).1 (inverseTransposePullback π)
    (firstDualFunctional ψ π ℓ) hinj''
    ⟨coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v', v', rfl⟩
    hv' B hBmem _

set_option maxHeartbeats 1000000 in
/-- The level of the zero-cell Kirillov lift. Let `π` be a generic representation of
`GL_(n+3)(F)`, `ψ` of conductor exponent zero, and suppose that for every norm-one tuple
`z` the symmetric gamma factor of `(π, I(z))` is `c^(n+2) (∏ z_i)^m X^((n+2) m)`. Then
every nonzero Whittaker functional `ℓ` of `π` has a model vector `w` that is fixed by
`K_1(m)` and agrees with the zero-cell function on the mirabolic subgroup. -/
theorem exists_levelFixed_zeroCellLift_of_unit_gamma
    (ψ : UnitaryAdditiveCharacter F.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
    (ν : AdditiveHaarMeasure F.Carrier) {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ (n + 2) π) (c : ℂˣ) (m : ℕ)
    (hG : ∀ z : Fin (n + 1 + 1) → ℂˣ, (∀ i, ‖(z i : ℂ)‖ = 1) →
      IsPadicSymmetricGammaFactor F ψ ν π (Unramified.principalSeriesOfTuple F z)
        (rationalEpsilonMonomial (c ^ (n + 2) * (∏ i, z i) ^ (m : ℤ))
          (((n + 2 : ℕ) : ℤ) * (m : ℤ)))) :
    ∃ ℓ : glFunctionals ψ (n + 2) π, ℓ.val ≠ 0 ∧
      ∃ w : (coefficientModel π ℓ).toSubmodule,
        (∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (n + 2) m →
          w.val.val (g * k) = w.val.val g) ∧
        ∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
          (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
          w.val.val g = (zeroCellWhittaker (Unramified.uniformizerUnit_isUniformizingElement F)
            hψ.1 (n + 2)).val g := by
  have hϖ := Unramified.uniformizerUnit_isUniformizingElement F
  have hψ' := Conductor.hasIntegerConductor_scale_neg_one hψ
  have hq : 1 < qF := PadicField.TopologicalData.residueCardinality_gt_one _
  have hq0 : 0 < qF := by omega
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  have hinj := isMirabolicRestrictionInjective_of_isGeneric F ψ π hπ ℓ hℓ
  obtain ⟨w, hw⟩ := exists_zeroCellLift F hϖ hψ.1 π hπ ℓ hℓ
  refine ⟨ℓ, hℓ, w, ?_, hw⟩
  -- The dual side: a zero-cell lift for `π^ι`.
  have hℓ'' : (firstDualFunctional ψ π ℓ).val ≠ 0 := firstDualFunctional_ne_zero ψ π hℓ
  have hgen'' : Whittaker.IsGeneric (ψ.scale (-1)) (n + 2) (inverseTransposePullback π) :=
    Conductor.isGeneric_inverseTransposePullback ψ π hπ
  have hinj'' := isMirabolicRestrictionInjective_of_isGeneric F (ψ.scale (-1))
    (inverseTransposePullback π) hgen'' (firstDualFunctional ψ π ℓ) hℓ''
  obtain ⟨W', hW'⟩ := exists_zeroCellLift F hϖ hψ'.1 (inverseTransposePullback π) hgen''
    (firstDualFunctional ψ π ℓ) hℓ''
  obtain ⟨v', hv'eq⟩ := W'.property
  have hv' : ∀ g : Langlands.GeneralLinear (n + 2 + 1) F.Carrier,
      (∀ j, g.val (Fin.last (n + 2)) j = if j = Fin.last (n + 2) then 1 else 0) →
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val g =
        (zeroCellWhittaker hϖ hψ'.1 (n + 2)).val g := by
    intro g hg
    have h1 : (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
        v').val g = W'.val.val g :=
      congrArg (fun f : WhittakerFunctions (ψ.scale (-1)) (n + 2) => f.val g) hv'eq
    rw [h1, hW' g hg]
  -- The comparison vector `Y` and the constant `C₀`.
  obtain ⟨Y, hYdef⟩ : ∃ Y : (coefficientModel π ℓ).toSubmodule,
      Y.val = coefficientMap π ℓ (inverseTransposePullback π
        (rankInclusion 1 (scalar (n := n + 2) (ϖF ^ (m : ℤ)))) v') :=
    ⟨⟨_, _, rfl⟩, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℂ, C₀ = (qF : ℂ) ^ (-((((n + 2 : ℕ) : ℤ) * (m : ℤ) : ℤ) : ℂ) / 2) *
      (qF : ℂ) ^ (((n + 2 : ℕ) : ℤ) * (m : ℤ)) / (c : ℂ) ^ (n + 2) := ⟨_, rfl⟩
  have hC₀ne : C₀ ≠ 0 := by
    have hq0' : (qF : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
    rw [hC₀]
    refine div_ne_zero (mul_ne_zero ?_ (zpow_ne_zero _ hq0')) (pow_ne_zero _ c.ne_zero)
    exact fun h => hq0' ((Complex.cpow_eq_zero_iff _ _).mp h).1
  -- Jacquet's normalization for the canonical uniformizer.
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier (n + 1)
  have hJ : Conductor.IsJacquetNormalization qF ψ abv ϖF
      (unipotentQuotientHaar F.Carrier (n + 1)) :=
    { residueCardinality := rfl
      uniformizer := hϖ
      abv_uniformizer := abv_uniformizerUnit F
      abv_unit := normalizedAbsoluteValue_eq_one F
      conductor := hψ
      measure := hμ
      borel := ⟨rfl⟩
      borel_rankOne := ⟨rfl⟩ }
  -- `U = w - C₀⁻¹ Y` has vanishing integrals for all norm-one `z`.
  have hzero : ∀ x : Fin (n + 1 + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) → ∃ a : ℝ, ∀ s : ℝ,
      a < s →
      CorankOneConverges ψ abv (unipotentQuotientHaar F.Carrier (n + 1)) (w - C₀⁻¹ • Y).val
          (Conductor.inverseSphericalWhittaker hJ.conductor.1 hJ.uniformizer qF x) s ∧
        corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier (n + 1)) (w - C₀⁻¹ • Y).val
          (Conductor.inverseSphericalWhittaker hJ.conductor.1 hJ.uniformizer qF x) s = 0 := by
    intro x hx
    obtain ⟨a, ha⟩ := forward_corankOne_dualTranslate_eq F ψ hψ ν π ℓ hℓ c m v' hv' x hx
      (hG x hx)
    have hint := integrable_integral_corankOneIntegrand_zeroCell F (n + 1)
      (unipotentQuotientHaar F.Carrier (n + 1)) hμ hϖ hψ.1
      (Conductor.inverseSphericalWhittaker hψ.1 hϖ qF x)
      (fun g k hk => Conductor.inverseSphericalWhittaker_mul_integral hψ.1 hϖ _ x g hk)
      (Conductor.inverseSphericalWhittaker_one hψ.1 hϖ _ x)
    have hrw : ∀ s, corankOneIntegrand ψ abv w.val
        (Conductor.inverseSphericalWhittaker hψ.1 hϖ qF x) s =
        corankOneIntegrand ψ abv (zeroCellWhittaker hϖ hψ.1 (n + 1 + 1))
          (Conductor.inverseSphericalWhittaker hψ.1 hϖ qF x) s :=
      fun s => corankOneIntegrand_eq_zeroCell hϖ hψ.1 w.val hw _ s
    refine ⟨a, fun s hs => ?_⟩
    have hs' : a < (s : ℂ).re := by rwa [Complex.ofReal_re]
    obtain ⟨hYc, hYi⟩ := ha s hs'
    rw [← hYdef] at hYc hYi
    rw [← hC₀] at hYi
    have hwc : CorankOneConverges ψ abv (unipotentQuotientHaar F.Carrier (n + 1)) w.val
        (Conductor.inverseSphericalWhittaker hψ.1 hϖ qF x) s := by
      unfold CorankOneConverges
      rw [hrw]
      exact (hint s).1
    have hwi : corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier (n + 1)) w.val
        (Conductor.inverseSphericalWhittaker hψ.1 hϖ qF x) s = 1 := by
      unfold corankOneIntegral
      rw [hrw]
      exact (hint s).2
    have hUval : (w - C₀⁻¹ • Y).val = w.val - C₀⁻¹ • Y.val := rfl
    rw [hUval]
    have hYc' := Conductor.CorankOneConverges.smul ψ abv
      (unipotentQuotientHaar F.Carrier (n + 1)) hYc C₀⁻¹
    refine ⟨Conductor.CorankOneConverges.sub ψ abv _ hwc hYc', ?_⟩
    rw [Conductor.corankOneIntegral_sub ψ abv _ hwc hYc', Conductor.corankOneIntegral_smul,
      hwi, hYi, inv_mul_cancel₀ hC₀ne, sub_self]
  -- `U` is restriction invariant.
  have hUinv : Conductor.IsIntegralInvariantOnRestriction π ℓ (w - C₀⁻¹ • Y) := by
    intro g k
    have hwk : w.val.val (rankInclusion 1 (g * k.val)) = w.val.val (rankInclusion 1 g) := by
      rw [map_mul]
      exact zeroCell_mul_fieldJacquetMirabolic hϖ hψ.1 π ℓ hinj w hw _
        ⟨rankInclusion_mem_integralSubgroup k.property, rankInclusion_lastRow _⟩ _
    have hYk : Y.val.val (rankInclusion 1 (g * k.val)) = Y.val.val (rankInclusion 1 g) := by
      rw [hYdef]
      exact dualTranslate_restriction_invariant F ψ hψ π ℓ hinj'' (ϖF ^ (m : ℤ)) v' hv' g k
    change w.val.val (rankInclusion 1 (g * k.val)) - C₀⁻¹ * Y.val.val
        (rankInclusion 1 (g * k.val)) =
      w.val.val (rankInclusion 1 g) - C₀⁻¹ * Y.val.val (rankInclusion 1 g)
    rw [hwk, hYk]
  -- Hence `U = 0`, i.e. `w = C₀⁻¹ Y`.
  have hUmir := eq_zero_on_mirabolic_of_unit_integrals_eq_zero (n := n + 1) hJ π hπ.2.1.1 ℓ
    (w - C₀⁻¹ • Y) hUinv hzero
  have hU0 : w - C₀⁻¹ • Y = 0 := Conductor.eq_zero_of_mirabolic_eq_zero π ℓ hinj _ hUmir
  have hwY : w = C₀⁻¹ • Y := sub_eq_zero.mp hU0
  -- The dual comparison and JPSS (5.3).
  have hdual : ∀ g, dualFunction (n + 2) w.val.val g = C₀⁻¹ *
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val
        (g * rankInclusion 1 (scalar (n := n + 2) (ϖF ^ (m : ℤ)))) := by
    intro g
    rw [dualFunction_apply, hwY]
    change C₀⁻¹ * Y.val.val _ = _
    rw [hYdef, coefficient_dualTranslate_apply, weylLong_inverseTranspose_involutive]
  have hP := mem_fixedVectors_fieldJacquetMirabolic_of_zeroCell hϖ hψ.1 π ℓ hinj w hw
  have hP' : ∀ k ∈ Conductor.fieldJacquetMirabolic (ValuativeRel.valuation F.Carrier).integer
      (n + 2), ∀ g, (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
        v').val (g * k) =
      (coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v').val g :=
    fun k hk g => zeroCell_mul_fieldJacquetMirabolic hϖ hψ'.1 (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ) hinj''
      ⟨coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v', v', rfl⟩
      hv' k hk g
  have hlev := Conductor.mem_levelFixedVectors_of_rankInclusion_dual_comparison (n := n + 1)
    ϖF hϖ m ψ π ℓ w _ C₀⁻¹ hdual hP hP'
  intro g k hk
  have he := (Conductor.mem_levelFixedVectors _ _ _).1 hlev k hk
  exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val g) he

end Padic

end Langlands.RankinSelberg.HighlyRamified
