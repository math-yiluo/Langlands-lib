import Langlands.Representation.RankinSelberg.UnitaryExponentBound
import Langlands.Representation.Whittaker.CharacterChange
import Langlands.HarmonicAnalysis.Conductor
import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Representation.RankinSelberg.UnramifiedPairStatement

/-!
# The unitary pole bound for unramified pairs
-/

noncomputable section

open Filter Topology

namespace Langlands.RankinSelberg.UnramifiedUnitary

open GeneralLinear GeneralLinear.Spherical Whittaker Conductor Correspondence HarmonicAnalysis
  Unramified

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance poleFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance poleFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance poleFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-! ### Valuations through the order -/

section Order

variable (T : F.TopologicalData)

theorem discreteValuation_eq_exp_neg_ord {x : F.Carrier} (hx : x ≠ 0) :
    T.discreteValuation x = WithZero.exp (-T.ord x) := by
  rw [PadicField.TopologicalData.ord, neg_neg,
    WithZero.exp_log ((T.discreteValuation.ne_zero_iff).mpr hx)]

theorem mem_integers_iff_ord {x : F.Carrier} (hx : x ≠ 0) :
    x ∈ T.Integers ↔ 0 ≤ T.ord x := by
  rw [T.mem_integers_iff_discreteValuation_le_one, discreteValuation_eq_exp_neg_ord F T hx,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem mem_additiveLattice_iff_ord {x : F.Carrier} (hx : x ≠ 0) (n : ℤ) :
    x ∈ T.additiveLattice n ↔ -T.ord x ≤ n := by
  rw [PadicField.TopologicalData.mem_additiveLattice, discreteValuation_eq_exp_neg_ord F T hx,
    WithZero.exp_le_exp]

end Order

/-! ### Change of additive character -/

/-- Every nontrivial additive character becomes of conductor `O` after scaling. -/
theorem exists_scale_hasIntegerConductor (ψ : UnitaryAdditiveCharacter F.Carrier) :
    ∃ a : F.Carrierˣ, HasIntegerConductor (ψ.scale a) := by
  let T := F.canonicalTopologicalData
  let c := T.additiveConductor ψ
  let ϖ := T.uniformizerUnit
  have ha0 : ((ϖ ^ (-c) : F.Carrierˣ) : F.Carrier) ≠ 0 := Units.ne_zero _
  have hord_a : T.ord ((ϖ ^ (-c) : F.Carrierˣ) : F.Carrier) = -c := by
    rw [Units.val_zpow_eq_zpow_val, T.ord_zpow]
    change -c * T.ord T.uniformizer = -c
    rw [T.ord_uniformizer, mul_one]
  have hψ0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ.toAddChar
  refine ⟨ϖ ^ (-c), fun x hx => ?_, fun x hx => ?_⟩
  · rw [UnitaryAdditiveCharacter.scale_apply]
    by_cases hx0 : x = 0
    · rw [hx0, mul_zero]
      exact hψ0
    · apply (T.additiveConductor_spec ψ).1
      rw [mem_additiveLattice_iff_ord F T (mul_ne_zero ha0 hx0), T.ord_mul ha0 hx0, hord_a]
      have := (mem_integers_iff_ord F T hx0).1 hx
      omega
  · by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ zero_mem _)
    have hordx : T.ord x < 0 := by
      by_contra h
      push Not at h
      exact hxO ((mem_integers_iff_ord F T hx0).2 h)
    obtain ⟨z, hz, hψz⟩ := T.exists_nontrivial_at_conductor_succ ψ
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hψz hψ0
    set a : F.Carrier := ((ϖ ^ (-c) : F.Carrierˣ) : F.Carrier)
    have hax : a * x ≠ 0 := mul_ne_zero ha0 hx0
    set y := z * (a * x)⁻¹ with hydef
    have hy0 : y ≠ 0 := mul_ne_zero hz0 (inv_ne_zero hax)
    have hyO : y ∈ (ValuativeRel.valuation F.Carrier).integer := by
      apply (mem_integers_iff_ord F T hy0).2
      rw [hydef, T.ord_mul hz0 (inv_ne_zero hax), T.ord_inv, T.ord_mul ha0 hx0, hord_a]
      have := (mem_additiveLattice_iff_ord F T hz0 _).1 hz
      omega
    apply hψz
    have h := hx y hyO
    rw [UnitaryAdditiveCharacter.scale_apply] at h
    have he : a * (x * y) = z := by
      rw [hydef]
      field_simp
    rw [← he]
    exact h

/-- Unramified generic constituents for `ψ` are also unramified generic constituents for
every scaled character `ψ.scale a`. -/
theorem isUnramifiedGenericConstituent_scale {r : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Fin (r + 1) → QuasiCharacter F) (hgen : IsUnramifiedGenericConstituent F ψ π χ)
    (a : F.Carrierˣ) : IsUnramifiedGenericConstituent F (ψ.scale a) π χ := by
  obtain ⟨⟨hirr, hadm, ℓ, hℓ⟩, hK, hχ, hsub⟩ := hgen
  refine ⟨⟨hirr, hadm, characterChangeFunctional ψ π a ℓ, ?_⟩, hK, hχ, hsub⟩
  intro h0
  apply hℓ
  ext w
  have h := LinearMap.congr_fun h0 (π (characterChangeElement a r)⁻¹ w)
  rw [characterChangeFunctional_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply] at h
  exact h

/-! ### Rank one -/

/-- For a unitarizable unramified generic constituent of `GL_1(F)`, the Satake parameter has
absolute value one. -/
theorem norm_unramifiedClass_rankOne {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F.Carrier) V)
    (χ : Fin (0 + 1) → QuasiCharacter F) (hgen : IsUnramifiedGenericConstituent F ψ σ χ)
    (hunit : IsUnitarizable σ) : ‖unramifiedClass F χ 0‖ = 1 := by
  classical
  obtain ⟨a, ha⟩ := exists_scale_hasIntegerConductor F ψ
  have hgen' := isUnramifiedGenericConstituent_scale F ψ σ χ hgen a
  have hirr : Representation.IsIrreducible σ := hgen'.1.1
  have hadm : IsAdmissible σ := hgen'.1.2.1
  obtain ⟨ℓ, hℓ⟩ := hgen'.1.2.2
  obtain ⟨w, -⟩ := (Langlands.RankinSelberg.unramifiedSphericalVector p F 0 σ (ψ.scale a) ha
    hgen'.1 hgen'.2.1).1 ℓ hℓ
  obtain ⟨v, hv⟩ := modelMap_surjective σ ℓ w.val.val
  have hval (g : Langlands.GeneralLinear (0 + 1) F.Carrier) :
      sphericalTestFunction σ ℓ w g = ℓ.val (σ g v) :=
    (congrArg (fun u : (coefficientModel σ ℓ).toSubmodule => u.val.val g) hv).symm
  have hvK : v ∈ fixedVectors σ (sphericalSubgroup F 0) :=
    UnramifiedWhittaker.mem_fixedVectors_of_model F σ ℓ (modelEquiv σ ℓ hℓ).injective v
      (by rw [hv]; exact (mem_sphericalModelSpace σ ℓ w.val.val).mp w.val.property)
  have hv1 : ℓ.val v = 1 := by
    have h := sphericalTestFunction_one σ ℓ w
    rw [hval, map_one, Module.End.one_apply] at h
    exact h
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, map_zero] at hv1
    exact zero_ne_one hv1
  -- the value at the uniformizer
  let t : Langlands.GeneralLinear (0 + 1) F.Carrier :=
    Iwasawa.torus F.canonicalTopologicalData.uniformizerUnit (fun _ => 1)
  have hα : UnramifiedWhittaker.IsPartitionExponent (fun _ : Fin (0 + 1) => (1 : ℤ)) :=
    ⟨fun _ _ _ => le_rfl, fun _ => zero_le_one⟩
  have hWt : ℓ.val (σ t v) = (characterValues F χ 0 : ℂ) := by
    rw [← hval, UnramifiedWhittaker.sphericalTest_torus_schur F σ (ψ.scale a) ha χ hgen' ℓ hℓ w _ hα]
    rw [halfModulus, satakeSchur]
    have hz : (fun i : Fin (0 + 1) => (1 : ℤ) - 1) = 0 := by
      funext i
      simp
    simp only [hz, jacobiTrudi_zero, map_one, mul_one, zpow_one]
    simp
  -- `σ(t) v` is spherical, hence a multiple of `v`
  have hcomm : ∀ g : Langlands.GeneralLinear (0 + 1) F.Carrier, g * t = t * g := by
    intro g
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have htK : σ t v ∈ fixedVectors σ (sphericalSubgroup F 0) := by
    intro k
    change σ k.val (σ t v) = σ t v
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    exact congrArg (σ t) (hvK k)
  obtain ⟨c, hc⟩ := UnramifiedWhittaker.fixedLine_of_isGeneric F σ hirr hadm hgen'.2.1 ⟨v, hvK⟩ ⟨σ t v, htK⟩
    (fun h => hv0 (congrArg Subtype.val h))
  have hc' : σ t v = c • v := (congrArg Subtype.val hc).symm
  have hcval : c = (characterValues F χ 0 : ℂ) := by
    rw [← hWt, hc', map_smul, hv1, smul_eq_mul, mul_one]
  -- unitarity
  obtain ⟨b⟩ := hunit
  have hinv := b.invariant t v v
  rw [hc'] at hinv
  have hbv : b.inner v v ≠ 0 := fun h => hv0 (b.definite v h)
  have hexp : b.inner (c • v) (c • v) = starRingEnd ℂ c * (c * b.inner v v) := by
    let := b.toInnerProductCore
    rw [b.smul_left]
    congr 1
    exact InnerProductSpace.Core.inner_smul_right v v
  rw [hexp, ← mul_assoc] at hinv
  have hcc : starRingEnd ℂ c * c = 1 := by
    have := mul_right_cancel₀ hbv (hinv.trans (one_mul _).symm)
    exact this
  have hn : ‖c‖ ^ 2 = 1 := by
    have h := congrArg Complex.re hcc
    rw [Complex.conj_mul'] at h
    exact_mod_cast h
  have hcn : ‖c‖ = 1 := by
    have h0 := norm_nonneg c
    nlinarith [sq_nonneg (‖c‖ - 1), sq_nonneg (‖c‖ + 1)]
  rw [← hcn, hcval]
  rfl

/-! ### The bounds for every additive character -/

/-- The Satake parameters of a unitarizable unramified generic constituent of `GL_(k+2)(F)`
satisfy `|a_i| < q^(1/2)`, for every nontrivial unitary additive character. -/
theorem norm_unramifiedClass_lt_sqrt (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (χ : Fin (k + 1 + 1) → QuasiCharacter F) (hgen : IsUnramifiedGenericConstituent F ψ π χ)
    (hunit : IsUnitarizable π) (i : Fin (k + 1 + 1)) :
    ‖unramifiedClass F χ i‖ < Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) := by
  obtain ⟨a, ha⟩ := exists_scale_hasIntegerConductor F ψ
  exact norm_characterValues_lt_sqrt F k π (ψ.scale a) ha χ
    (isUnramifiedGenericConstituent_scale F ψ π χ hgen a) hunit i

/-- The Satake parameters of a unitarizable unramified generic constituent of `GL_(n+1)(F)`
satisfy `|a_j| ≤ q^(1/2)`. -/
theorem norm_unramifiedClass_le_sqrt (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (χ : Fin (n + 1) → QuasiCharacter F) (hgen : IsUnramifiedGenericConstituent F ψ σ χ)
    (hunit : IsUnitarizable σ) (j : Fin (n + 1)) :
    ‖unramifiedClass F χ j‖ ≤ Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) := by
  cases n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst hj
    rw [norm_unramifiedClass_rankOne F ψ σ χ hgen hunit]
    rw [Real.one_le_sqrt]
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  | succ k => exact (norm_unramifiedClass_lt_sqrt F k ψ σ χ hgen hunit j).le

end Langlands.RankinSelberg.UnramifiedUnitary

namespace Langlands.RankinSelberg

open UnramifiedUnitary

universe uF uV uW

/-- **Jacquet–Shalika, Euler products II, Proposition 1.5(iii).** For unitarizable unramified
generic `π` of `GL_(t+1)(F)` and `σ` of `GL_(n+1)(F)` with `n < t`, the Euler factor
`∏ (1 - a_i b_j q^(-s))` does not vanish for `Re s ≥ 1`. -/
theorem unramifiedUnitaryPoleFree : UnramifiedUnitaryPoleFreeStatement.{uF, uV, uW} := by
  intro p _ F t n hnt V _ _ W _ _ π σ χ χ' ψ hπ hσ huπ huσ s hs
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  set q := F.canonicalTopologicalData.residueCardinality
  have hq1 : 1 < q := F.canonicalTopologicalData.residueCardinality_gt_one
  have hq : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq1)
  have hsq : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq
  have hss : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = q := Real.mul_self_sqrt hq.le
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ (q : ℝ)⁻¹ := by
    rw [Complex.norm_natCast_cpow_of_pos (lt_trans Nat.zero_lt_one hq1), Complex.neg_re]
    calc (q : ℝ) ^ (-s.re) ≤ (q : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq1.le) (by linarith)
      _ = (q : ℝ)⁻¹ := Real.rpow_neg_one _
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have ha := norm_unramifiedClass_lt_sqrt F k ψ π χ hπ huπ i
  have hb := norm_unramifiedClass_le_sqrt F n ψ σ χ' hσ huσ j
  have hab : ‖unramifiedClass F χ i‖ * ‖unramifiedClass F χ' j‖ < q := by
    calc ‖unramifiedClass F χ i‖ * ‖unramifiedClass F χ' j‖
        ≤ ‖unramifiedClass F χ i‖ * Real.sqrt (q : ℝ) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ < Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) := mul_lt_mul_of_pos_right ha hsq
      _ = q := hss
  have hz : ‖unramifiedClass F χ i * unramifiedClass F χ' j * (q : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, norm_mul]
    calc ‖unramifiedClass F χ i‖ * ‖unramifiedClass F χ' j‖ * ‖(q : ℂ) ^ (-s)‖
        ≤ ‖unramifiedClass F χ i‖ * ‖unramifiedClass F χ' j‖ * (q : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ < q * (q : ℝ)⁻¹ := mul_lt_mul_of_pos_right hab (inv_pos.mpr hq)
      _ = 1 := mul_inv_cancel₀ hq.ne'
  intro h0
  have h1 : unramifiedClass F χ i * unramifiedClass F χ' j * (q : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp h0).symm
  rw [h1, norm_one] at hz
  exact lt_irrefl _ hz

end Langlands.RankinSelberg
