import Langlands.Representation.RankinSelberg.CommonLevelRootSupport
import Langlands.AllField.Group.GL.PadicSupplement
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof
/-! # Uniform simple-root bounds from a common right level -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg.CommonLevel hiding exists_uniform_lattice root_bound
open Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg
open Langlands.AllField.RankinSelberg

open Matrix _root_.Topology
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open scoped WithZero

universe uF

/-- A single small additive lattice works for all integral conjugates of every
simple-root subgroup. Only openness of the supplied level is needed. -/
theorem exists_uniform_lattice 
    (F : Type uF) [Field F] (T : LocalFieldData F) (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (K : Subgroup (Langlands.GeneralLinear (r + 1) F)),
      IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F)) →
      ∃ n : ℤ, ∀ t ∈ T.additiveLattice n,
        ∀ κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer r,
          ∀ i : Fin r, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro K hK
  let L := Conductor.levelOpenSubgroup F r 0
  have hL : IsCompact (L : Set (Langlands.GeneralLinear (r + 1) F)) :=
    Conductor.isCompact_levelOpenSubgroup F r 0
  have hev (i : Fin r) : ∀ᶠ t in 𝓝 (0 : F),
      ∀ κ ∈ L, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K := by
    apply hL.eventually_forall_of_forall_eventually
    intro κ _
    have hc : Continuous (fun x : F × Langlands.GeneralLinear (r + 1) F =>
        x.2⁻¹ * (simpleRootUnipotent i x.1).val * x.2) :=
      (continuous_snd.inv.mul ((simpleRootUnipotent_continuous i).comp continuous_fst)).mul
        continuous_snd
    exact hc.continuousAt.preimage_mem_nhds (hK.mem_nhds (by
      simp only [simpleRootUnipotent_zero, mul_one, inv_mul_cancel]
      exact K.one_mem))
  have hall : {t : F | ∀ i : Fin r,
      ∀ κ ∈ L, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K} ∈ 𝓝 (0 : F) :=
    Filter.eventually_all.mpr hev
  obtain ⟨n, hn⟩ := T.exists_additiveLattice_subset hall
  refine ⟨n, fun t ht κ hκ i => hn ht i κ ?_⟩
  change κ ∈ Conductor.levelSubgroup F r 0
  rwa [Conductor.levelSubgroup_zero]

/-- The common level bounds all adjacent diagonal ratios at every nonzero value,
uniformly over the entire supplied family and the integral factor. -/
theorem root_bound 
    (F : Type uF) [Field F] (T : LocalFieldData F) (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (U : ℂ → WhittakerFunctions ψ r)
      (K : Subgroup (Langlands.GeneralLinear (r + 1) F)),
      IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F)) →
      (∀ z g (k : K), (U z).val (g * k) = (U z).val g) →
      ∃ R : ℝ, 0 < R ∧ ∀ z (a : Fin (r + 1) → Fˣ) κ,
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer r →
        (U z).val (Iwasawa.diagonalUnits a * κ) ≠ 0 →
        ∀ i : Fin r,
          T.normalizedAbs ((a i.castSucc / a i.succ : Fˣ) : F) ≤ R := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ U K hK hU
  obtain ⟨n, hn⟩ := exists_uniform_lattice F T r K hK
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  refine ⟨(T.residueCardinality : ℝ) ^ (T.additiveConductor ψ - n),
    zpow_pos (lt_trans zero_lt_one hq) _, ?_⟩
  intro z a κ hκ hnonzero i
  let c : F := ((a i.castSucc / a i.succ : Fˣ) : F)
  have hc : c ≠ 0 := (a i.castSucc / a i.succ).ne_zero
  have hchar (t : F) (ht : t ∈ T.additiveLattice n) :
      ψ.complex (c * t) = 1 := by
    have hfix := hU z (Iwasawa.diagonalUnits a * κ)
      ⟨κ⁻¹ * (simpleRootUnipotent i t).val * κ, hn t ht κ hκ i⟩
    have heq : (U z).val ((simpleRootUnipotent i (c * t)).val *
        (Iwasawa.diagonalUnits a * κ)) = (U z).val (Iwasawa.diagonalUnits a * κ) := by
      rw [← mul_assoc, ← diagonal_simpleRootUnipotent a i t, mul_assoc]
      simpa only [Subgroup.coe_mk, mul_assoc, mul_inv_cancel_left] using hfix
    rw [(U z).property, simpleRootUnipotent_character] at heq
    exact mul_right_cancel₀ hnonzero (heq.trans (one_mul _).symm)
  have hvc : T.discreteValuation c ≠ 0 := (T.discreteValuation.ne_zero_iff).mpr hc
  have htriv : T.AdditiveTrivialAt ψ (WithZero.log (T.discreteValuation c) + n) := by
    intro x hx
    have ht : x / c ∈ T.additiveLattice n := by
      change T.discreteValuation (x / c) ≤ WithZero.exp n
      rw [map_div₀, div_le_iff₀ (zero_lt_iff.mpr hvc)]
      rw [← WithZero.exp_log hvc]
      simpa only [Langlands.LocalFieldData.mem_additiveLattice,
        WithZero.exp_add, mul_comm] using hx
    apply Subtype.ext
    have hcx : c * (x / c) = x := by field_simp
    simpa [hcx] using hchar (x / c) ht
  have hle := (T.additiveTrivialAt_iff_le_conductor ψ _).mp htriv
  change T.normalizedAbs c ≤ _
  rw [T.normalizedAbs_of_ne_zero hc]
  apply (zpow_le_zpow_iff_right₀ hq).mpr
  change -(-WithZero.log (T.discreteValuation c)) ≤ T.additiveConductor ψ - n
  omega

end Langlands.AllField.RankinSelberg.CommonLevel
