import Langlands.LocalField.Normalization.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Complete arithmetic normalization, beginning with residue and discrete-order laws. -/

namespace Langlands.PadicField.TopologicalData

open scoped WithZero

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem finite_residueField : Finite T.ResidueField := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact inferInstanceAs (Finite (IsLocalRing.ResidueField
    (ValuativeRel.valuation F.Carrier).integer))

theorem residueCardinality_gt_one : 1 < T.residueCardinality := by
  let := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  simpa [residueCardinality, Nat.card_eq_fintype_card] using
    (Fintype.one_lt_card : 1 < Fintype.card T.ResidueField)

theorem residueDegree_pos : 0 < T.residueDegree := by
  let := T.residueAlgebra
  let := T.finite_residueField
  exact Module.finrank_pos

theorem residueCardinality_eq_pow : T.residueCardinality = p ^ T.residueDegree := by
  let := T.residueAlgebra
  let := T.finite_residueField
  simpa [residueCardinality, residueDegree, Nat.card_eq_fintype_card, ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := ZMod p) (V := T.ResidueField))

theorem residueScalarMap_injective : Function.Injective T.residueScalarMap :=
  T.residueScalarMap.injective

theorem discreteValuation_surjective : Function.Surjective T.discreteValuation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).surjective.comp
    ValuativeRel.valuation_surjective

theorem discreteValuation_uniformizer :
    T.discreteValuation T.uniformizer = WithZero.exp (-1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have h : ValuativeRel.valuation F.Carrier T.uniformizer =
      e.symm (WithZero.exp (-1)) :=
    (ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))).choose_spec
  change e (ValuativeRel.valuation F.Carrier T.uniformizer) = WithZero.exp (-1)
  rw [h, e.apply_symm_apply]

theorem ord_zero : T.ord 0 = 0 := by simp [ord]

theorem ord_one : T.ord 1 = 0 := by simp [ord]

theorem ord_uniformizer : T.ord T.uniformizer = 1 := by
  simp [ord, T.discreteValuation_uniformizer]

theorem ord_mul {x y : F.Carrier} (hx : x ≠ 0) (hy : y ≠ 0) :
    T.ord (x * y) = T.ord x + T.ord y := by
  simp [ord, map_mul, WithZero.log_mul
    ((T.discreteValuation.ne_zero_iff).mpr hx)
    ((T.discreteValuation.ne_zero_iff).mpr hy), add_comm]

theorem ord_inv (x : F.Carrier) : T.ord x⁻¹ = -T.ord x := by
  simp [ord, map_inv₀, WithZero.log_inv]

theorem min_ord_le_ord_add {x y : F.Carrier} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (T.ord x) (T.ord y) ≤ T.ord (x + y) := by
  change min (-WithZero.log (T.discreteValuation x)) (-WithZero.log (T.discreteValuation y)) ≤
    -WithZero.log (T.discreteValuation (x + y))
  rcases le_max_iff.mp (T.discreteValuation.map_add x y) with h | h
  · exact (min_le_left _ _).trans (neg_le_neg ((WithZero.log_le_log
      (T.discreteValuation.ne_zero_iff.mpr hxy) (T.discreteValuation.ne_zero_iff.mpr hx)).mpr h))
  · exact (min_le_right _ _).trans (neg_le_neg ((WithZero.log_le_log
      (T.discreteValuation.ne_zero_iff.mpr hxy) (T.discreteValuation.ne_zero_iff.mpr hy)).mpr h))

theorem ord_surjective_nonzero (n : ℤ) : ∃ x : F.Carrier, x ≠ 0 ∧ T.ord x = n := by
  obtain ⟨x, hx⟩ := T.discreteValuation_surjective (WithZero.exp (-n))
  refine ⟨x, ?_, ?_⟩
  · intro h
    exact WithZero.exp_ne_zero (by rw [← hx, h, map_zero])
  · simp [ord, hx]

theorem ord_prime_pos : 0 < T.ord (p : F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.valuativeExtension
  let := T.localField
  have hp0 : (p : F.Carrier) ≠ 0 := by
    simpa only [map_natCast] using
      ((map_ne_zero (algebraMap (Padic p) F.Carrier)).mpr
        (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : Padic p) ≠ 0))
  have hp : (p : Padic p) <ᵥ 1 := by
    rw [(ValuativeRel.valuation (Padic p)).vlt_one_iff]
    exact Padic.valuation_p_lt_one _
  have hF : ValuativeRel.valuation F.Carrier (p : F.Carrier) < 1 := by
    rw [← (ValuativeRel.valuation F.Carrier).vlt_one_iff]
    simpa only [map_natCast, map_one] using
      (ValuativeExtension.vlt_iff_vlt (A := Padic p) (B := F.Carrier)).mpr hp
  have hd : T.discreteValuation (p : F.Carrier) < 1 := by
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier (p : F.Carrier)) < 1
    simpa only [map_one] using
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono hF
  apply neg_pos.mpr
  exact (WithZero.log_lt_iff_lt_exp ((T.discreteValuation.ne_zero_iff).mpr hp0)).mpr
    (by simpa only [WithZero.exp_zero] using hd)

theorem ramificationIndex_pos : 0 < T.ramificationIndex :=
  Int.pos_iff_toNat_pos.mp T.ord_prime_pos

theorem ramificationIndex_cast : (T.ramificationIndex : ℤ) = T.ord (p : F.Carrier) :=
  Int.toNat_of_nonneg T.ord_prime_pos.le

theorem normalizedAbs_zero : T.normalizedAbs 0 = 0 := by simp [normalizedAbs]

theorem normalizedAbs_one : T.normalizedAbs 1 = 1 := by
  simp [normalizedAbs, T.ord_one]

theorem normalizedAbs_of_ne_zero {x : F.Carrier} (hx : x ≠ 0) :
    T.normalizedAbs x = (T.residueCardinality : ℝ) ^ (-T.ord x) := by
  simp [normalizedAbs, hx]

theorem normalizedAbs_pos {x : F.Carrier} (hx : x ≠ 0) : 0 < T.normalizedAbs x := by
  rw [T.normalizedAbs_of_ne_zero hx]
  exact zpow_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)) _

theorem normalizedAbs_nonneg (x : F.Carrier) : 0 ≤ T.normalizedAbs x := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  exact (T.normalizedAbs_pos hx).le

theorem normalizedAbs_le_iff_of_ne_zero {x y : F.Carrier} (hx : x ≠ 0) (hy : y ≠ 0) :
    T.normalizedAbs x ≤ T.normalizedAbs y ↔
      T.discreteValuation x ≤ T.discreteValuation y := by
  rw [T.normalizedAbs_of_ne_zero hx, T.normalizedAbs_of_ne_zero hy]
  simp only [ord, neg_neg]
  rw [zpow_le_zpow_iff_right₀ (by exact_mod_cast T.residueCardinality_gt_one)]
  exact WithZero.log_le_log ((T.discreteValuation.ne_zero_iff).mpr hx)
    ((T.discreteValuation.ne_zero_iff).mpr hy)

theorem normalizedAbs_mul (x y : F.Carrier) :
    T.normalizedAbs (x * y) = T.normalizedAbs x * T.normalizedAbs y := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  by_cases hy : y = 0
  · simp [hy, T.normalizedAbs_zero]
  rw [T.normalizedAbs_of_ne_zero (mul_ne_zero hx hy),
    T.normalizedAbs_of_ne_zero hx, T.normalizedAbs_of_ne_zero hy,
    T.ord_mul hx hy, neg_add, zpow_add₀]
  exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'

theorem normalizedAbs_add_le_max (x y : F.Carrier) :
    T.normalizedAbs (x + y) ≤ max (T.normalizedAbs x) (T.normalizedAbs y) := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  by_cases hy : y = 0
  · simp [hy, T.normalizedAbs_zero]
  by_cases hxy : x + y = 0
  · rw [hxy, T.normalizedAbs_zero]
    exact le_trans (T.normalizedAbs_nonneg x) (le_max_left _ _)
  rcases le_max_iff.mp (T.discreteValuation.map_add x y) with h | h
  · exact le_max_of_le_left ((T.normalizedAbs_le_iff_of_ne_zero hxy hx).mpr h)
  · exact le_max_of_le_right ((T.normalizedAbs_le_iff_of_ne_zero hxy hy).mpr h)

theorem normalizedAbs_uniformizer :
    T.normalizedAbs T.uniformizer = (T.residueCardinality : ℝ) ^ (-1 : ℤ) := by
  have hπ : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  rw [T.normalizedAbs_of_ne_zero hπ, T.ord_uniformizer]

end Langlands.PadicField.TopologicalData

namespace Langlands

theorem padicNormalizationBasic : PadicNormalizationBasicStatement.{u} := by
  intro p hp F T
  have hfin := T.finite_residueField
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨T.residueCharP, hfin, ?_, T.residueScalarMap_injective,
      T.residueDegree_pos, T.residueCardinality_gt_one, T.residueCardinality_eq_pow⟩
    let := T.residueAlgebra
    exact inferInstance
  · exact ⟨T.discreteValuation_surjective, T.discreteValuation_uniformizer,
      T.ord_zero, T.ord_one, T.ord_uniformizer, fun _ _ hx hy => T.ord_mul hx hy,
      T.ord_inv, fun _ _ hx hy hxy => T.min_ord_le_ord_add hx hy hxy,
      T.ord_surjective_nonzero, T.ord_prime_pos, T.ramificationIndex_pos, T.ramificationIndex_cast⟩
  · exact ⟨T.normalizedAbs_zero, T.normalizedAbs_one, T.normalizedAbs_nonneg,
      fun _ hx => T.normalizedAbs_pos hx, fun _ hx => T.normalizedAbs_of_ne_zero hx,
      T.normalizedAbs_mul, T.normalizedAbs_add_le_max, T.normalizedAbs_uniformizer⟩

end Langlands

/-! Private development of the comparison with the base-extending spectral norm. -/

namespace Langlands.PadicField.TopologicalData

open scoped WithZero

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem ord_zpow (x : F.Carrier) (n : ℤ) : T.ord (x ^ n) = n * T.ord x := by
  simp [ord, map_zpow₀, WithZero.log_zpow, mul_neg]

theorem ord_algebraMap (a : Padic p) :
    T.ord (algebraMap (Padic p) F.Carrier a) =
      (T.ramificationIndex : ℤ) * a.valuation := by
  let := T.topology
  let := T.valuativeRel
  let := T.valuativeExtension
  let := T.localField
  by_cases ha : a = 0
  · simp [ha, T.ord_zero]
  have hp : (p : Padic p) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv : Padic.mulValuation a =
      Padic.mulValuation ((p : Padic p) ^ a.valuation) := by
    simp [Padic.mulValuation, ha, hp]
  have he : algebraMap (Padic p) F.Carrier a =ᵥ
      algebraMap (Padic p) F.Carrier ((p : Padic p) ^ a.valuation) := by
    simp only [ValuativeRel.veq_def, ValuativeExtension.vle_iff_vle,
      Padic.mulValuation.vle_iff_le]
    exact ⟨hv.le, hv.ge⟩
  have hd : T.discreteValuation (algebraMap (Padic p) F.Carrier a) =
      T.discreteValuation (algebraMap (Padic p) F.Carrier
        ((p : Padic p) ^ a.valuation)) := by
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (ValuativeRel.valuation F.Carrier (algebraMap (Padic p) F.Carrier a)) =
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (ValuativeRel.valuation F.Carrier (algebraMap (Padic p) F.Carrier
          ((p : Padic p) ^ a.valuation)))
    exact congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      ((ValuativeRel.valuation F.Carrier).veq_iff_eq.mp he)
  have ho := congrArg (fun z => -WithZero.log z) hd
  change T.ord (algebraMap (Padic p) F.Carrier a) =
    T.ord (algebraMap (Padic p) F.Carrier ((p : Padic p) ^ a.valuation)) at ho
  simpa only [map_zpow₀, map_natCast, T.ord_zpow, T.ramificationIndex_cast,
    mul_comm] using ho

theorem normalizedAbs_eq_zero_iff (x : F.Carrier) :
    T.normalizedAbs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (T.normalizedAbs_pos hx).ne' h
  · rintro rfl
    exact T.normalizedAbs_zero

private noncomputable def rescaledAbs (s : ℝ) (hs : 0 < s) :
    AbsoluteValue F.Carrier ℝ where
  toFun x := (T.normalizedAbs x) ^ s
  map_mul' x y := by
    rw [T.normalizedAbs_mul, Real.mul_rpow (T.normalizedAbs_nonneg x)
      (T.normalizedAbs_nonneg y)]
  nonneg' x := Real.rpow_nonneg (T.normalizedAbs_nonneg x) s
  eq_zero' x := by
    rw [Real.rpow_eq_zero (T.normalizedAbs_nonneg x) hs.ne', T.normalizedAbs_eq_zero_iff]
  add_le' x y := by
    calc
      (T.normalizedAbs (x + y)) ^ s ≤
          (max (T.normalizedAbs x) (T.normalizedAbs y)) ^ s :=
        Real.rpow_le_rpow (T.normalizedAbs_nonneg _) (T.normalizedAbs_add_le_max x y) hs.le
      _ = max ((T.normalizedAbs x) ^ s) ((T.normalizedAbs y) ^ s) :=
        Real.rpow_max (T.normalizedAbs_nonneg x) (T.normalizedAbs_nonneg y) hs.le
      _ ≤ (T.normalizedAbs x) ^ s + (T.normalizedAbs y) ^ s :=
        max_le (le_add_of_nonneg_right (Real.rpow_nonneg (T.normalizedAbs_nonneg y) s))
          (le_add_of_nonneg_left (Real.rpow_nonneg (T.normalizedAbs_nonneg x) s))

theorem normalizedAbs_algebraMap (a : Padic p) (ha : a ≠ 0) :
    T.normalizedAbs (algebraMap (Padic p) F.Carrier a) =
      ‖a‖ ^ (T.ramificationIndex * T.residueDegree) := by
  rw [T.normalizedAbs_of_ne_zero ((map_ne_zero _).mpr ha),
    T.ord_algebraMap, T.residueCardinality_eq_pow,
    Nat.cast_pow, Padic.norm_eq_zpow_neg_valuation ha]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem normalizedAbs_eq_canonicalNorm_pow_ef (x : F.Carrier) :
    T.normalizedAbs x = F.canonicalNorm x ^ (T.ramificationIndex * T.residueDegree) := by
  let n := T.ramificationIndex * T.residueDegree
  have hn : 0 < n := Nat.mul_pos T.ramificationIndex_pos T.residueDegree_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let abv := T.rescaledAbs (n : ℝ)⁻¹ (inv_pos.mpr hnR)
  have hext : ∀ a : Padic p, abv (algebraMap (Padic p) F.Carrier a) = ‖a‖ := by
    intro a
    change (T.normalizedAbs (algebraMap (Padic p) F.Carrier a)) ^ (n : ℝ)⁻¹ = ‖a‖
    by_cases ha : a = 0
    · simp [ha, T.normalizedAbs_zero, ne_of_gt hnR]
    rw [T.normalizedAbs_algebraMap a ha]
    exact Real.pow_rpow_inv_natCast (norm_nonneg a) hn.ne'
  have heq := spectralNorm_unique_field_norm_ext hext x
  change (T.normalizedAbs x) ^ (n : ℝ)⁻¹ = F.canonicalNorm x at heq
  rw [← heq]
  exact (Real.rpow_inv_natCast_pow (T.normalizedAbs_nonneg x) hn.ne').symm

end Langlands.PadicField.TopologicalData

/-! The actual integer ring as an integral closure. -/

namespace Langlands.PadicField.TopologicalData

open scoped WithZero
open Polynomial

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem normalizedAbs_le_one_iff_mem_integers (x : F.Carrier) :
    T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  have h := T.normalizedAbs_le_iff_of_ne_zero hx (one_ne_zero : (1 : F.Carrier) ≠ 0)
  rw [T.normalizedAbs_one, map_one] at h
  rw [h]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier x) ≤ 1 ↔
    ValuativeRel.valuation F.Carrier x ≤ 1
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono.le_iff_le

theorem canonicalNorm_le_one_iff_mem_integers (x : F.Carrier) :
    F.canonicalNorm x ≤ 1 ↔ x ∈ T.Integers := by
  have hn : T.ramificationIndex * T.residueDegree ≠ 0 :=
    (Nat.mul_pos T.ramificationIndex_pos T.residueDegree_pos).ne'
  rw [← pow_le_one_iff_of_nonneg (show 0 ≤ F.canonicalNorm x from
      spectralNorm_nonneg (K := Padic p) (L := F.Carrier) x) hn,
    ← T.normalizedAbs_eq_canonicalNorm_pow_ef x]
  exact T.normalizedAbs_le_one_iff_mem_integers x

theorem baseInteger_mem_iff_norm_le_one (a : Padic p) :
    a ∈ (ValuativeRel.valuation (Padic p)).integer ↔ ‖a‖ ≤ 1 := by
  have h : 1 < ValuativeRel.valuation (Padic p) a ↔ 1 < ‖a‖ := by
    rw [← (ValuativeRel.valuation (Padic p)).one_vlt_iff,
      Padic.mulValuation.one_vlt_iff, ← map_one (Padic.mulValuation (p := p)),
      ← Padic.norm_lt_norm_iff_mulValuation_lt, norm_one]
  simpa only [Valuation.mem_integer_iff, not_lt] using not_congr h

theorem isIntegral_iff_mem_integers (x : F.Carrier) :
    letI := Algebra.compHom F.Carrier (algebraMap
      (ValuativeRel.valuation (Padic p)).integer (Padic p))
    IsIntegral (ValuativeRel.valuation (Padic p)).integer x ↔ x ∈ T.Integers := by
  let := T.valuativeRel
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom F.Carrier (algebraMap A (Padic p))
  let := T.integerAlgebra
  let : IsScalarTower A (Padic p) F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A T.Integers F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  constructor
  · intro hx
    exact (Valuation.integer.integers (ValuativeRel.valuation F.Carrier)).isIntegral_iff_v_le_one.mp
      (hx.tower_top (A := T.Integers))
  · intro hx
    have hn := (T.canonicalNorm_le_one_iff_mem_integers x).mpr hx
    have hm : (minpoly (Padic p) x).Monic :=
      minpoly.monic (Algebra.IsIntegral.isIntegral x)
    have hc : ∀ n, ‖(minpoly (Padic p) x).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff hm).mp hn
    have hl : minpoly (Padic p) x ∈ Polynomial.lifts (algebraMap A (Padic p)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, (baseInteger_mem_iff_norm_le_one _).mpr (hc n)⟩, rfl⟩
    obtain ⟨g, hg, _, hgm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
    refine ⟨g, hgm, ?_⟩
    have he := minpoly.aeval (Padic p) x
    rw [← hg, Polynomial.aeval_map_algebraMap] at he
    exact he

theorem integers_isIntegralClosure :
    letI := Algebra.compHom F.Carrier (algebraMap
      (ValuativeRel.valuation (Padic p)).integer (Padic p))
    IsIntegralClosure T.Integers (ValuativeRel.valuation (Padic p)).integer F.Carrier := by
  let := T.valuativeRel
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom F.Carrier (algebraMap A (Padic p))
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  rw [T.isIntegral_iff_mem_integers]
  exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

theorem integers_finite :
    letI := T.integerAlgebra
    Module.Finite (ValuativeRel.valuation (Padic p)).integer T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom F.Carrier (algebraMap A (Padic p))
  let := T.integerAlgebra
  let : IsScalarTower A (Padic p) F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A T.Integers F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := T.integers_isIntegralClosure
  exact IsIntegralClosure.finite A (Padic p) F.Carrier T.Integers

theorem integers_free :
    letI := T.integerAlgebra
    Module.Free (ValuativeRel.valuation (Padic p)).integer T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom F.Carrier (algebraMap A (Padic p))
  let := T.integerAlgebra
  let : IsScalarTower A (Padic p) F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A T.Integers F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := T.integers_isIntegralClosure
  let : Module.IsTorsionFree A F.Carrier :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (Padic p) F.Carrier).injective.comp Subtype.val_injective)
  exact IsIntegralClosure.module_free A (Padic p) F.Carrier T.Integers

theorem integers_finrank :
    letI := T.integerAlgebra
    Module.finrank (ValuativeRel.valuation (Padic p)).integer T.Integers =
      Module.finrank (Padic p) F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom F.Carrier (algebraMap A (Padic p))
  let := T.integerAlgebra
  let : IsScalarTower A (Padic p) F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A T.Integers F.Carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := T.integers_isIntegralClosure
  let : Module.IsTorsionFree A F.Carrier :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      ((algebraMap (Padic p) F.Carrier).injective.comp Subtype.val_injective)
  exact IsIntegralClosure.rank A (Padic p) F.Carrier T.Integers

noncomputable def baseIntegerEquivPadicInt :
    (ValuativeRel.valuation (Padic p)).integer ≃+* PadicInt p where
  toFun a := ⟨a, (baseInteger_mem_iff_norm_le_one _).mp a.property⟩
  invFun a := ⟨a, (baseInteger_mem_iff_norm_le_one _).mpr a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

noncomputable def baseResidueEquivZMod :
    IsLocalRing.ResidueField (ValuativeRel.valuation (Padic p)).integer ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv (baseIntegerEquivPadicInt (p := p))).trans PadicInt.residueField

end Langlands.PadicField.TopologicalData

/-! The ramification-inertia degree formula. -/

namespace Langlands.PadicField.TopologicalData

open scoped WithZero

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

private theorem discreteValuation_integers : T.discreteValuation.Integers T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let i := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  refine ⟨Subtype.val_injective, ?_, ?_⟩
  · intro x
    change i (ValuativeRel.valuation F.Carrier x.val) ≤ 1
    rw [← map_one i]
    exact i.strictMono.monotone x.property
  · intro x hx
    change i (ValuativeRel.valuation F.Carrier x) ≤ 1 at hx
    rw [← map_one i] at hx
    exact ⟨⟨x, i.strictMono.le_iff_le.mp hx⟩, rfl⟩

private noncomputable def uniformizerInteger : T.Integers :=
  (T.discreteValuation_integers.exists_of_le_one
    (r := T.uniformizer) (by rw [T.discreteValuation_uniformizer]; norm_num)).choose

private theorem uniformizerInteger_coe :
    (T.uniformizerInteger : F.Carrier) = T.uniformizer :=
  (T.discreteValuation_integers.exists_of_le_one
    (r := T.uniformizer) (by rw [T.discreteValuation_uniformizer]; norm_num)).choose_spec

private theorem maximalIdeal_eq_span_uniformizer :
    IsLocalRing.maximalIdeal T.Integers = Ideal.span {T.uniformizerInteger} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x ↔ x ∈ Ideal.span {T.uniformizerInteger}
  rw [T.discreteValuation_integers.isUnit_iff_valuation_eq_one]
  rw [← SetLike.mem_coe, T.discreteValuation_integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  change T.discreteValuation x.val ≠ 1 ↔
    T.discreteValuation x.val ≤ T.discreteValuation T.uniformizerInteger.val
  rw [T.uniformizerInteger_coe, T.discreteValuation_uniformizer]
  have hle := T.discreteValuation_integers.map_le_one x
  have hstep : T.discreteValuation x.val < 1 ↔
      T.discreteValuation x.val ≤ WithZero.exp (-1) := by
    simpa [← WithZero.exp_add] using
      (WithZero.lt_mul_exp_iff_le (x := T.discreteValuation x.val)
        (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
  rw [← hstep]
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩

private theorem uniformizerInteger_irreducible : Irreducible T.uniformizerInteger := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    T.maximalIdeal_eq_span_uniformizer

private theorem discreteValuation_prime :
    T.discreteValuation (p : F.Carrier) = WithZero.exp (-1) ^ T.ramificationIndex := by
  have hpv : T.discreteValuation (p : F.Carrier) ≠ 0 := by
    intro h
    have hp := T.ord_prime_pos
    simp [ord, h] at hp
  rw [← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one, T.ramificationIndex_cast]
  simpa only [ord, neg_neg] using (WithZero.exp_log hpv).symm

theorem span_prime_eq_maximalIdeal_pow :
    Ideal.span {(p : T.Integers)} =
      IsLocalRing.maximalIdeal T.Integers ^ T.ramificationIndex := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply SetLike.coe_injective
  rw [T.discreteValuation_integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap,
    T.discreteValuation_integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      T.uniformizerInteger_irreducible]
  change {x : T.Integers | T.discreteValuation x.val ≤
      T.discreteValuation (p : F.Carrier)} =
    {x : T.Integers | T.discreteValuation x.val ≤
      T.discreteValuation T.uniformizerInteger.val ^ T.ramificationIndex}
  rw [T.uniformizerInteger_coe, T.discreteValuation_uniformizer, T.discreteValuation_prime]

private theorem prime_not_mem_maximalIdeal_succ :
    (p : T.Integers) ∉
      IsLocalRing.maximalIdeal T.Integers ^ (T.ramificationIndex + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [← SetLike.mem_coe,
    T.discreteValuation_integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow
      T.uniformizerInteger_irreducible]
  change ¬ T.discreteValuation (p : F.Carrier) ≤
    T.discreteValuation T.uniformizerInteger.val ^ (T.ramificationIndex + 1)
  rw [T.uniformizerInteger_coe, T.discreteValuation_uniformizer, T.discreteValuation_prime]
  simp [← WithZero.exp_nsmul]

private theorem base_prime_irreducible :
    Irreducible (p : (ValuativeRel.valuation (Padic p)).integer) := by
  apply (MulEquiv.irreducible_iff (baseIntegerEquivPadicInt (p := p))).mp
  simpa only [map_natCast] using (PadicInt.irreducible_p (p := p))

theorem map_base_maximalIdeal :
    letI := T.integerAlgebra
    (IsLocalRing.maximalIdeal (ValuativeRel.valuation (Padic p)).integer).map
      (algebraMap (ValuativeRel.valuation (Padic p)).integer T.Integers) =
      IsLocalRing.maximalIdeal T.Integers ^ T.ramificationIndex := by
  let := T.integerAlgebra
  rw [(base_prime_irreducible (p := p)).maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, map_natCast]
  exact T.span_prime_eq_maximalIdeal_pow

private theorem baseIntegerMap_injective : Function.Injective T.baseIntegerMap := by
  intro a b h
  apply Subtype.ext
  exact (algebraMap (Padic p) F.Carrier).injective (congrArg Subtype.val h)

theorem ramificationIdx_eq :
    letI := T.integerAlgebra
    (IsLocalRing.maximalIdeal T.Integers).ramificationIdx
      (ValuativeRel.valuation (Padic p)).integer = T.ramificationIndex := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  let := T.integers_finite
  let : Module.IsTorsionFree A T.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr T.baseIntegerMap_injective
  have hA : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    rw [(base_prime_irreducible (p := p)).maximalIdeal_eq]
    exact Ideal.span_singleton_eq_bot.not.mpr (base_prime_irreducible (p := p)).ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal T.Integers) hA]
  apply Ideal.ramificationIdx'_spec
  · rw [T.map_base_maximalIdeal]
  · intro h
    apply T.prime_not_mem_maximalIdeal_succ
    apply h
    rw [T.map_base_maximalIdeal, ← T.span_prime_eq_maximalIdeal_pow]
    exact Ideal.subset_span (Set.mem_singleton _)

theorem inertiaDeg_eq :
    letI := T.integerAlgebra
    (IsLocalRing.maximalIdeal T.Integers).inertiaDeg
      (ValuativeRel.valuation (Padic p)).integer = T.residueDegree := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  let := T.integers_finite
  let : Module.IsTorsionFree A T.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr T.baseIntegerMap_injective
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal T.Integers)]
  have hbase : Nat.card (IsLocalRing.ResidueField A) = p := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using
      Nat.card_congr (baseResidueEquivZMod (p := p)).toEquiv
  let := T.finite_residueField
  have hcard := Module.natCard_eq_pow_finrank
    (K := IsLocalRing.ResidueField A) (V := T.ResidueField)
  rw [hbase] at hcard
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  exact hcard.symm.trans T.residueCardinality_eq_pow

theorem ramificationIndex_mul_residueDegree :
    T.ramificationIndex * T.residueDegree = Module.finrank (Padic p) F.Carrier := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  let := T.integers_finite
  let := T.integers_free
  let : Module.IsTorsionFree A T.Integers :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr T.baseIntegerMap_injective
  have hA : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    rw [(base_prime_irreducible (p := p)).maximalIdeal_eq]
    exact Ideal.span_singleton_eq_bot.not.mpr (base_prime_irreducible (p := p)).ne_zero
  have hprimes := IsLocalRing.primesOver_eq (A := T.Integers) hA
  let q : (IsLocalRing.maximalIdeal A).primesOver T.Integers :=
    ⟨IsLocalRing.maximalIdeal T.Integers, by rw [hprimes]; exact Set.mem_singleton _⟩
  let : Unique ((IsLocalRing.maximalIdeal A).primesOver T.Integers) :=
    { default := q
      uniq := fun r => Subtype.ext (by simpa only [hprimes, Set.mem_singleton_iff] using r.property) }
  let := Fintype.ofFinite ((IsLocalRing.maximalIdeal A).primesOver T.Integers)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal A) T.Integers
  simp only [Fintype.sum_unique] at hsum
  change (IsLocalRing.maximalIdeal T.Integers).ramificationIdx A *
    (IsLocalRing.maximalIdeal T.Integers).inertiaDeg A = Module.finrank A T.Integers at hsum
  rw [T.ramificationIdx_eq, T.inertiaDeg_eq, T.integers_finrank] at hsum
  exact hsum

theorem normalizedAbs_eq_canonicalNorm_pow_degree (x : F.Carrier) :
    T.normalizedAbs x = F.canonicalNorm x ^ Module.finrank (Padic p) F.Carrier := by
  rw [T.normalizedAbs_eq_canonicalNorm_pow_ef, T.ramificationIndex_mul_residueDegree]

end Langlands.PadicField.TopologicalData

/-! Topology and base-normalization comparison proofs. -/

namespace Langlands.PadicField.TopologicalData

open scoped Topology

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

theorem extensionDegree_pos : 0 < Module.finrank (Padic p) F.Carrier :=
  Module.finrank_pos

theorem normalizedAbs_algebraMap_degree (a : Padic p) :
    T.normalizedAbs (algebraMap (Padic p) F.Carrier a) =
      ‖a‖ ^ Module.finrank (Padic p) F.Carrier := by
  by_cases ha : a = 0
  · rw [ha, map_zero, T.normalizedAbs_zero, norm_zero,
      zero_pow (extensionDegree_pos (F := F)).ne']
  · rw [T.normalizedAbs_algebraMap a ha, T.ramificationIndex_mul_residueDegree]

theorem normalizedAbs_eq_canonicalNorm_of_degree_one
    (h : Module.finrank (Padic p) F.Carrier = 1) (x : F.Carrier) :
    T.normalizedAbs x = F.canonicalNorm x := by
  rw [T.normalizedAbs_eq_canonicalNorm_pow_degree, h, pow_one]

theorem indices_eq_one_of_degree_one
    (h : Module.finrank (Padic p) F.Carrier = 1) :
    T.ramificationIndex = 1 ∧ T.residueDegree = 1 := by
  exact (mul_eq_one_iff_of_one_le T.ramificationIndex_pos T.residueDegree_pos).mp
    (T.ramificationIndex_mul_residueDegree.trans h)

theorem residueCardinality_eq_prime_of_degree_one
    (h : Module.finrank (Padic p) F.Carrier = 1) :
    T.residueCardinality = p := by
  rw [T.residueCardinality_eq_pow, (T.indices_eq_one_of_degree_one h).2, pow_one]

theorem topology_eq_canonicalModule : T.topology = F.canonicalTopology := by
  let := T.topology
  let := T.moduleTopology
  exact eq_moduleTopology (Padic p) F.Carrier

theorem topology_eq_canonicalNormTopology :
    T.topology = (letI := F.canonicalNormedField
      inferInstance : TopologicalSpace F.Carrier) := by
  let := F.canonicalNormedField
  let := F.canonicalNormedAlgebra
  let : IsModuleTopology (Padic p) F.Carrier := isModuleTopologyOfFiniteDimensional
  exact T.topology_eq_canonicalModule.trans (eq_moduleTopology (Padic p) F.Carrier).symm

theorem normalizedAbs_balls_basis :
    letI := T.topology
    TopologicalSpace.IsTopologicalBasis
      {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
        0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  have habs (x : F.Carrier) :
      T.normalizedAbs x = ‖x‖ ^ Module.finrank (Padic p) F.Carrier :=
    T.normalizedAbs_eq_canonicalNorm_pow_degree x
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨a, ε, _, rfl⟩
    have hc : Continuous (fun x : F.Carrier => T.normalizedAbs (x - a)) := by
      simp_rw [habs]
      exact ((continuous_id.sub continuous_const).norm).pow _
    exact isOpen_lt hc continuous_const
  · intro a U ha hU
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU a ha
    refine ⟨{x | T.normalizedAbs (x - a) < δ ^ Module.finrank (Padic p) F.Carrier},
      ⟨a, _, pow_pos hδ _, rfl⟩, ?_, ?_⟩
    · simpa only [Set.mem_ofPred_eq, sub_self, T.normalizedAbs_zero] using pow_pos hδ
        (Module.finrank (Padic p) F.Carrier)
    · intro y hy
      apply hsub
      rw [Metric.mem_ball, dist_eq_norm]
      rw [Set.mem_ofPred_eq, habs] at hy
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le
        (extensionDegree_pos (F := F)).ne').mp hy

theorem normalizedAbs_topology_eq :
    TopologicalSpace.generateFrom
      {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
        0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} = T.topology := by
  let := T.topology
  exact T.normalizedAbs_balls_basis.eq_generateFrom.symm

theorem normalizedAbs_topology_eq_canonicalModule :
    TopologicalSpace.generateFrom
      {U : Set F.Carrier | ∃ (a : F.Carrier) (ε : ℝ),
        0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} = F.canonicalTopology :=
  T.normalizedAbs_topology_eq.trans T.topology_eq_canonicalModule

end Langlands.PadicField.TopologicalData

namespace Langlands

/-- The complete arithmetic and topology normalization for finite p-adic fields. -/
theorem padicNormalization : PadicNormalizationStatement.{u} := by
  intro p hp F T
  have hb := padicNormalizationBasic p F T
  refine ⟨hb.1, hb.2.1, hb.2.2, ?_, ?_, ?_, ?_⟩
  · exact ⟨T.integers_isIntegralClosure, T.isIntegral_iff_mem_integers,
      ⟨T.integers_finite, T.integers_free, T.integers_finrank⟩,
      T.normalizedAbs_le_one_iff_mem_integers, T.canonicalNorm_le_one_iff_mem_integers⟩
  · exact ⟨T.span_prime_eq_maximalIdeal_pow, T.map_base_maximalIdeal,
      ⟨T.ramificationIdx_eq, T.inertiaDeg_eq⟩, T.ramificationIndex_mul_residueDegree,
      PadicField.TopologicalData.extensionDegree_pos (F := F)⟩
  · refine ⟨T.ord_algebraMap, T.normalizedAbs_algebraMap_degree,
      T.normalizedAbs_eq_canonicalNorm_pow_degree, ?_⟩
    intro h
    exact ⟨(T.indices_eq_one_of_degree_one h).1, (T.indices_eq_one_of_degree_one h).2,
      T.residueCardinality_eq_prime_of_degree_one h,
      T.normalizedAbs_eq_canonicalNorm_of_degree_one h⟩
  · exact ⟨T.topology_eq_canonicalModule, T.topology_eq_canonicalNormTopology,
      T.normalizedAbs_balls_basis, T.normalizedAbs_topology_eq,
      T.normalizedAbs_topology_eq_canonicalModule⟩

end Langlands
