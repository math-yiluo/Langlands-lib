import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! # Uniform simple-root bounds from a common right level -/

noncomputable section

namespace Langlands.RankinSelberg.CommonLevel

open GeneralLinear HarmonicAnalysis Whittaker Matrix Topology
open scoped WithZero

universe uF

def simpleRootUnipotent {K : Type*} [Field K] {r : ℕ}
    (i : Fin r) (t : K) : upperUnipotent (r + 1) K :=
  ⟨⟨transvection i.castSucc i.succ t, transvection i.castSucc i.succ (-t),
      by rw [transvection_mul_transvection_same _ _ (ne_of_lt i.castSucc_lt_succ),
        add_neg_cancel, transvection_zero],
      by rw [transvection_mul_transvection_same _ _ (ne_of_lt i.castSucc_lt_succ),
        neg_add_cancel, transvection_zero]⟩,
    by
      constructor
      · intro a b hab
        change transvection i.castSucc i.succ t a b = 0
        have hab' : a ≠ b := ne_of_gt hab
        have hroot : ¬ (i.castSucc = a ∧ i.succ = b) := by
          rintro ⟨rfl, rfl⟩
          exact (not_lt_of_ge i.castSucc_lt_succ.le) hab
        simp [transvection, hab', hroot]
      · intro a
        change transvection i.castSucc i.succ t a a = 1
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, ite_true,
          Matrix.single_apply]
        split_ifs with h
        · exact False.elim ((ne_of_lt i.castSucc_lt_succ) (h.1.trans h.2.symm))
        · simp⟩

theorem simpleRootUnipotent_zero {K : Type*} [Field K] {r : ℕ} (i : Fin r) :
    (simpleRootUnipotent i (0 : K)).val = 1 := by
  apply Units.ext
  exact transvection_zero _ _

theorem simpleRootUnipotent_continuous {K : Type*} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] {r : ℕ} (i : Fin r) :
    Continuous (fun t : K => (simpleRootUnipotent i t).val) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro a <;> apply continuous_pi <;> intro b
  · change Continuous (fun t : K => transvection i.castSucc i.succ t a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · change Continuous (fun t : K => transvection i.castSucc i.succ (-t) a b)
    simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem simpleRootUnipotent_character {K : Type*} [Field K]
    [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K) {r : ℕ}
    (i : Fin r) (t : K) :
    (standardCharacter ψ r (simpleRootUnipotent i t) : ℂ) = ψ.complex t := by
  rw [standardCharacter_apply]
  congr 1
  change (∑ j : Fin r, transvection i.castSucc i.succ t j.castSucc j.succ) = t
  have hentry (j : Fin r) :
      transvection i.castSucc i.succ t j.castSucc j.succ = if j = i then t else 0 := by
    simp [transvection, Matrix.single_apply,
      ne_of_lt j.castSucc_lt_succ, eq_comm]
  simp_rw [hentry]
  simp

theorem diagonal_simpleRootUnipotent {K : Type*} [Field K] {r : ℕ}
    (a : Fin (r + 1) → Kˣ) (i : Fin r) (t : K) :
    Iwasawa.diagonalUnits a * (simpleRootUnipotent i t).val =
      (simpleRootUnipotent i (((a i.castSucc / a i.succ : Kˣ) : K) * t)).val *
        Iwasawa.diagonalUnits a := by
  apply Units.ext
  change diagonal (fun j => (a j : K)) * transvection i.castSucc i.succ t =
    transvection i.castSucc i.succ (((a i.castSucc / a i.succ : Kˣ) : K) * t) *
      diagonal (fun j => (a j : K))
  ext j k
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Units.val_div_eq_div_val]
  by_cases hj : i.castSucc = j <;> by_cases hk : i.succ = k <;> by_cases hjk : j = k
    <;> simp_all [ne_of_lt i.castSucc_lt_succ, eq_comm]
  field_simp

/-- A single small additive lattice works for all integral conjugates of every
simple-root subgroup. Only openness of the supplied level is needed. -/
theorem exists_uniform_lattice {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (K : Subgroup (Langlands.GeneralLinear (r + 1) F.Carrier)),
      IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) →
      ∃ n : ℤ, ∀ t ∈ T.additiveLattice n,
        ∀ κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r,
          ∀ i : Fin r, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro K hK
  let L := Conductor.levelOpenSubgroup F.Carrier r 0
  have hL : IsCompact (L : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) :=
    Conductor.isCompact_levelOpenSubgroup F.Carrier r 0
  have hev (i : Fin r) : ∀ᶠ t in 𝓝 (0 : F.Carrier),
      ∀ κ ∈ L, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K := by
    apply hL.eventually_forall_of_forall_eventually
    intro κ _
    have hc : Continuous (fun x : F.Carrier × Langlands.GeneralLinear (r + 1) F.Carrier =>
        x.2⁻¹ * (simpleRootUnipotent i x.1).val * x.2) :=
      (continuous_snd.inv.mul ((simpleRootUnipotent_continuous i).comp continuous_fst)).mul
        continuous_snd
    exact hc.continuousAt.preimage_mem_nhds (hK.mem_nhds (by
      simp only [simpleRootUnipotent_zero, mul_one, inv_mul_cancel]
      exact K.one_mem))
  have hall : {t : F.Carrier | ∀ i : Fin r,
      ∀ κ ∈ L, κ⁻¹ * (simpleRootUnipotent i t).val * κ ∈ K} ∈ 𝓝 (0 : F.Carrier) :=
    Filter.eventually_all.mpr hev
  obtain ⟨n, hn⟩ := T.exists_additiveLattice_subset hall
  refine ⟨n, fun t ht κ hκ i => hn ht i κ ?_⟩
  change κ ∈ Conductor.levelSubgroup F.Carrier r 0
  rwa [Conductor.levelSubgroup_zero]

/-- The common level bounds all adjacent diagonal ratios at every nonzero value,
uniformly over the entire supplied family and the integral factor. -/
theorem root_bound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (U : ℂ → WhittakerFunctions ψ r)
      (K : Subgroup (Langlands.GeneralLinear (r + 1) F.Carrier)),
      IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) →
      (∀ z g (k : K), (U z).val (g * k) = (U z).val g) →
      ∃ R : ℝ, 0 < R ∧ ∀ z (a : Fin (r + 1) → F.Carrierˣ) κ,
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r →
        (U z).val (Iwasawa.diagonalUnits a * κ) ≠ 0 →
        ∀ i : Fin r,
          T.normalizedAbs ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) ≤ R := by
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
  let c : F.Carrier := ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
  have hc : c ≠ 0 := (a i.castSucc / a i.succ).ne_zero
  have hchar (t : F.Carrier) (ht : t ∈ T.additiveLattice n) :
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
      simpa only [PadicField.TopologicalData.mem_additiveLattice,
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

end Langlands.RankinSelberg.CommonLevel
