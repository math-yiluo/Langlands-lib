import Langlands.BushnellKutzko.StratumZetaIntegral
import Langlands.BushnellKutzko.CompactLevelBound
import Langlands.Representation.Conductor.ClassLevel
import Langlands.Representation.Classification.SupercuspidalStrata
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # The Swan conductor and the normalized level in rank one

For an irreducible supercuspidal class `π` of `GL_1(K)` with normalized level `x`, the first
fixed level of `π` is a natural number `c` with `c - 1 = x` (truncated subtraction):
`exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne`. This is T2 in rank one.

The proof only compares subgroups of `GL_1(K) = K^×`. For every lattice chain `𝓛` in `K^1`
with period `e` and every `m`, the level subgroup `1 + 𝔭^{c}` with `c = ⌊m/e⌋ + 1` lies in
`U^{m+1}(𝔄(𝓛))` (`levelSubgroup_le_unitSubgroup`); and for the standard chain `𝔭^i`, whose
period is one, `U^c(𝔄) ≤ 1 + 𝔭^c` for `c ≥ 1` (`unitSubgroup_standard_le_levelSubgroup`).
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uK uV

section General

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In rank one, `toLin'(y - 1)` is multiplication by the scalar `y₀₀ - 1`. -/
theorem toLin'_sub_one_rankOne (y : Matrix (Fin 1) (Fin 1) F) :
    Matrix.toLin' (y - 1) = (y 0 0 - 1) • (1 : Module.End F (Fin 1 → F)) := by
  refine LinearMap.ext fun v => funext fun i => ?_
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, sub_mul]

include hϖ in
/-- A nonzero element of `𝔭^c` has order at least `c`. -/
theorem le_ordOf_of_mem_maximalIdeal_pow {c : ℕ} {y : 𝒪[F]}
    (hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F] ^ c) (hy0 : (y : F) ≠ 0) :
    (c : ℤ) ≤ ordOf hϖ (y : F) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨z, rfl⟩ := hy
  have hz : (z : F) ≠ 0 := by
    intro h
    apply hy0
    rw [Subring.coe_mul, h, zero_mul]
  rw [Subring.coe_mul, SubmonoidClass.coe_pow,
    ordOf_mul hϖ hz (pow_ne_zero _ (coe_uniformizer_ne_zero hϖ)), ← zpow_natCast, ordOf_zpow]
  linarith [ordOf_nonneg hϖ hz z.2]

include hϖ in
/-- The standard lattice chain `L_i = ϖ^i 𝔬_F^ι` has period one. -/
theorem LatticeChain.standard_period (ι : Type*) [Fintype ι] [Nonempty ι] :
    (LatticeChain.standard hϖ ι).period = 1 := by
  refine ((LatticeChain.standard hϖ ι).period_unique (e := 1) fun i => ?_).symm
  show (LatticeChain.uniformizerAsUnit hϖ ^ (i + ((1 : ℕ) : ℤ))) •
      LatticeChain.standardLattice F ι =
    Ring.jacobson 𝒪[F] • ((LatticeChain.uniformizerAsUnit hϖ ^ i) •
      LatticeChain.standardLattice F ι)
  rw [jacobson_integer_eq_maximalIdeal, hϖ.maximalIdeal_eq,
    Submodule.ideal_span_singleton_smul, Nat.cast_one, add_comm, zpow_one_add, mul_smul]
  ext v
  simp only [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    ext k
    simp [Subring.smul_def]
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    ext k
    simp [Subring.smul_def]

end General

section Padic

local instance roTopologicalSpace {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance roValuativeRel {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel

local instance roLocalField {p : ℕ} [Fact p.Prime] (F : PadicField p) :
    IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- For a lattice chain `𝓛` in `K^1` with period `e` and `m + 1 ≤ e c`, the level
subgroup `1 + 𝔭^c` of `GL_1(K)` lies in `U^{m+1}(𝔄(𝓛))`. -/
theorem levelSubgroup_le_unitSubgroup {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    (𝓛 : LatticeChain 𝒪[K.Carrier] K.Carrier (Fin 1 → K.Carrier)) {c m : ℕ}
    (hm : m + 1 ≤ 𝓛.period * c) :
    Conductor.levelSubgroup K.Carrier 0 c ≤ unitSubgroup K 𝓛 (m + 1) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Conductor.mem_integralCongruence_rankOne] at hh
  rw [mem_unitSubgroup_iff_sub_one_mem K 𝓛 (by omega), LatticeChain.mem_matrixFiltration,
    toLin'_sub_one_rankOne]
  have hd : (Matrix.GeneralLinearGroup.map (ValuativeRel.valuation K.Carrier).integer.subtype
      h).val 0 0 - 1 =
      ((((h : Matrix (Fin 1) (Fin 1) 𝒪[K.Carrier]) 0 0 - 1 : 𝒪[K.Carrier])) : K.Carrier) := by
    rfl
  rw [hd]
  set d : 𝒪[K.Carrier] := (h : Matrix (Fin 1) (Fin 1) 𝒪[K.Carrier]) 0 0 - 1
  by_cases hd0 : (d : K.Carrier) = 0
  · rw [hd0, zero_smul]
    exact zero_mem _
  · have hord := le_ordOf_of_mem_maximalIdeal_pow hϖ hh hd0
    have h1 : (1 : Module.End K.Carrier (Fin 1 → K.Carrier)) ∈ 𝓛.endFiltration 0 :=
      𝓛.order.one_mem
    refine 𝓛.endFiltration_antitone ?_ (𝓛.smul_mem_endFiltration_ordOf hϖ hd0 h1)
    have hm' : ((m : ℤ) + 1) ≤ (𝓛.period : ℤ) * c := by exact_mod_cast hm
    have he : (0 : ℤ) ≤ 𝓛.period := by positivity
    push_cast
    nlinarith

/-- For the standard chain `𝔭^i` in `K^1` and `c ≥ 1`, `U^c(𝔄) ≤ 1 + 𝔭^c` in `GL_1(K)`. -/
theorem unitSubgroup_standard_le_levelSubgroup {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    {c : ℕ} (hc : 1 ≤ c) :
    unitSubgroup K (LatticeChain.standard hϖ (Fin 1)) c ≤
      Conductor.levelSubgroup K.Carrier 0 c := by
  intro g hg
  rw [mem_unitSubgroup_iff_sub_one_mem K _ hc, LatticeChain.mem_matrixFiltration,
    toLin'_sub_one_rankOne] at hg
  set d : K.Carrier := g.val 0 0 - 1 with hd
  have hv : (fun _ => (1 : K.Carrier)) ∈ (LatticeChain.standard hϖ (Fin 1)).lattice 0 := by
    rw [LatticeChain.mem_standard_lattice]
    intro k
    simp
  have h2 := (LatticeChain.mem_standard_lattice hϖ).1 (hg 0 _ hv) 0
  have hϖc : ((ϖ : K.Carrier)) ^ c ≠ 0 := pow_ne_zero _ (coe_uniformizer_ne_zero hϖ)
  have key : ((ϖ : K.Carrier) ^ c)⁻¹ * d ∈ 𝒪[K.Carrier] := by
    convert h2 using 1
    simp [LatticeChain.uniformizerAsUnit]
  have hdmem : d ∈ 𝒪[K.Carrier] := by
    have : d = (ϖ : K.Carrier) ^ c * (((ϖ : K.Carrier) ^ c)⁻¹ * d) := by
      field_simp
    rw [this]
    exact mul_mem (pow_mem ϖ.2 c) key
  set d' : 𝒪[K.Carrier] := ⟨d, hdmem⟩
  have hd' : d' ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] ^ c := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨_, key⟩, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, d']
    field_simp
  have hmax : d' ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] :=
    Ideal.pow_le_self (by omega) hd'
  have hunit : IsUnit (1 + d') := by
    by_contra hnu
    have h1 : 1 + d' ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] := hnu
    have : (1 : 𝒪[K.Carrier]) ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] := by
      simpa using sub_mem h1 hmax
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[K.Carrier]).ne_top
      ((Ideal.eq_top_iff_one _).2 this)
  refine Subgroup.mem_map.mpr ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) hunit.unit, ?_, ?_⟩
  · rw [Conductor.mem_integralCongruence_rankOne]
    simpa using hd'
  · ext i j
    have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi hj
    simp [d', hd]

/-- Fixed vectors of a smaller subgroup. -/
theorem hasFixedVector_of_le_rankOne {H H' : Subgroup (GeneralLinear 1 K.Carrier)} (hle : H' ≤ H)
    {a : SmoothDualClass.{0, uK, uV} (k := ℂ) (G := GeneralLinear 1 K.Carrier)}
    (ha : SmoothDualClass.HasFixedVector H a) : SmoothDualClass.HasFixedVector H' a := by
  induction a using Quotient.inductionOn with
  | h A =>
    change fixedVectors A.obj.representation H ≠ ⊥ at ha
    change fixedVectors A.obj.representation H' ≠ ⊥
    intro hbot
    apply ha
    rw [eq_bot_iff, ← hbot]
    exact fixedVectors_antitone A.obj.representation hle

/-- **T2 in rank one.** Let `π` be an irreducible supercuspidal class of `GL_1(K)` with
normalized level `x`. Then the first fixed level of `π` is a natural number `c`, and
`c - 1 = x` (truncated subtraction). -/
theorem exists_firstFixedLevel_eq_of_isNormalizedLevel_rankOne
    (π : GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := 0 + 1)) {x : ℚ}
    (hlev : IsNormalizedLevel K (0 + 1) (GeneralLinear.SupercuspidalClass.toSmoothDualClass π)
      x) :
    ∃ c : ℕ, GeneralLinear.SupercuspidalClass.firstFixedLevel π = (c : WithTop ℕ) ∧
      ((c - (0 + 1) : ℕ) : ℚ) = ((0 + 1 : ℕ) : ℚ) * x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K.Carrier]
  set a := GeneralLinear.SupercuspidalClass.toSmoothDualClass π with ha
  obtain ⟨𝓛₀, m₀, hx₀, hfix₀⟩ := hlev.1
  have he₀ : 0 < 𝓛₀.period := 𝓛₀.period_pos
  have hle1 : m₀ + 1 ≤ 𝓛₀.period * (m₀ / 𝓛₀.period + 1) := Nat.lt_mul_div_succ m₀ he₀
  have hfix1 : SmoothDualClass.HasFixedVector
      (Conductor.levelSubgroup K.Carrier 0 (m₀ / 𝓛₀.period + 1)) a :=
    hasFixedVector_of_le_rankOne K (levelSubgroup_le_unitSubgroup K hϖ 𝓛₀ hle1) hfix₀
  have hff : GeneralLinear.SupercuspidalClass.firstFixedLevel π ≤
      ((m₀ / 𝓛₀.period + 1 : ℕ) : WithTop ℕ) :=
    (GeneralLinear.SupercuspidalClass.firstFixedLevel_le_iff π _).2 hfix1
  obtain ⟨c, hc⟩ : ∃ c : ℕ, GeneralLinear.SupercuspidalClass.firstFixedLevel π = c := by
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hff)
    exact ⟨c, hc.symm⟩
  refine ⟨c, hc, ?_⟩
  have hcle : c ≤ m₀ / 𝓛₀.period + 1 := by
    rw [hc] at hff
    exact_mod_cast hff
  have hfixc : SmoothDualClass.HasFixedVector (Conductor.levelSubgroup K.Carrier 0 c) a :=
    (GeneralLinear.SupercuspidalClass.firstFixedLevel_le_iff π c).1 hc.le
  apply le_antisymm
  · rw [hx₀]
    calc ((c - (0 + 1) : ℕ) : ℚ) ≤ ((m₀ / 𝓛₀.period : ℕ) : ℚ) := by
          have hq : c - (0 + 1) ≤ m₀ / 𝓛₀.period := by
            generalize m₀ / 𝓛₀.period = q at hcle ⊢
            omega
          exact_mod_cast hq
      _ ≤ (m₀ : ℚ) / 𝓛₀.period := Nat.cast_div_le
      _ = ((0 + 1 : ℕ) : ℚ) * ((m₀ : ℚ) / 𝓛₀.period) := by simp
  · have hc1 : 1 ≤ max c 1 := le_max_right _ _
    have hfix2 : SmoothDualClass.HasFixedVector
        (unitSubgroup K (LatticeChain.standard hϖ (Fin 1)) (max c 1 - 1 + 1)) a := by
      rw [Nat.sub_add_cancel hc1]
      exact hasFixedVector_of_le_rankOne K (unitSubgroup_standard_le_levelSubgroup K hϖ hc1)
        (hasFixedVector_of_le_rankOne K (Conductor.levelSubgroup_antitone _ _ (le_max_left c 1)) hfixc)
    have hmem : (((max c 1 - 1 : ℕ) : ℚ) / ((LatticeChain.standard hϖ (Fin 1)).period : ℚ)) ∈
        normalizedLevelValues K (0 + 1) a := ⟨_, _, rfl, hfix2⟩
    have hle := hlev.2 hmem
    rw [LatticeChain.standard_period hϖ (Fin 1)] at hle
    have hmc : max c 1 - 1 = c - (0 + 1) := by omega
    rw [hmc] at hle
    simpa using hle

end Padic

end Langlands.BushnellKutzko
