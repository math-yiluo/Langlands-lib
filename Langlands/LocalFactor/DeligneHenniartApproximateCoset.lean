import Langlands.LocalFactor.DeligneHenniartExactCoset

/-! # The approximate Deligne--Henniart witness coset -/

noncomputable section

open scoped WithZero

universe uF uV

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The base prime has valuation at most `exp (-1)`. -/
theorem discreteValuation_prime_le :
    T.discreteValuation (p : F.Carrier) ≤ WithZero.exp (-1) := by
  have h := T.ord_prime_pos
  apply WithZero.le_exp_of_log_le
  unfold ord at h
  omega

/-- The `p`th power of a principal unit of positive level `n` has level `n + 1`. -/
theorem pow_prime_mem_principalUnits_succ {n : ℕ} (hn : 1 ≤ n) {u : F.Carrierˣ}
    (hu : u ∈ T.principalUnits n) : u ^ p ∈ T.principalUnits (n + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨hu1, hux⟩ := hu
  have hx1 : T.discreteValuation ((u : F.Carrier) - 1) ≤ 1 :=
    hux.trans (WithZero.exp_le_one_iff.mpr (by omega))
  have hxI : (u : F.Carrier) - 1 ∈ T.Integers :=
    (T.mem_integers_iff_discreteValuation_le_one _).mpr hx1
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime)
    (⟨(u : F.Carrier) - 1, hxI⟩ : T.Integers) 1
  have hr' : (u : F.Carrier) ^ p =
      ((u : F.Carrier) - 1) ^ p + 1 + p * ((u : F.Carrier) - 1) * r := by
    have h := congrArg Subtype.val hr
    simp only [one_pow, mul_one] at h
    push_cast at h
    rw [← h]
    ring
  have hr1 : T.discreteValuation (r : F.Carrier) ≤ 1 :=
    (T.mem_integers_iff_discreteValuation_le_one _).mp r.2
  refine ⟨by rw [Units.val_pow_eq_pow_val, map_pow, hu1, one_pow], ?_⟩
  have heq : ((u ^ p : F.Carrierˣ) : F.Carrier) - 1 =
      ((u : F.Carrier) - 1) ^ p + p * ((u : F.Carrier) - 1) * r := by
    rw [Units.val_pow_eq_pow_val, hr']
    ring
  have hp2 := (Fact.out : p.Prime).two_le
  rw [heq]
  apply T.discreteValuation.map_add_le
  · rw [map_pow]
    calc T.discreteValuation ((u : F.Carrier) - 1) ^ p
        ≤ WithZero.exp (-(n : ℤ)) ^ p := pow_le_pow_left₀ zero_le hux p
      _ = WithZero.exp (p • -(n : ℤ)) := (WithZero.exp_nsmul _ _).symm
      _ ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
        rw [WithZero.exp_le_exp, nsmul_eq_mul]
        push_cast
        have : (2 : ℤ) ≤ p := by exact_mod_cast hp2
        nlinarith
  · rw [map_mul, map_mul]
    calc T.discreteValuation (p : F.Carrier) * T.discreteValuation ((u : F.Carrier) - 1) *
          T.discreteValuation (r : F.Carrier)
        ≤ WithZero.exp (-1) * WithZero.exp (-(n : ℤ)) * 1 := by
          gcongr
          exact T.discreteValuation_prime_le
      _ = WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_add]
        congr 1
        push_cast
        ring

/-- Iterating: a unit of level one raised to `p ^ k` has level `k + 1`. -/
theorem pow_prime_pow_mem_principalUnits {u : F.Carrierˣ} (hu : u ∈ T.principalUnits 1)
    (k : ℕ) : u ^ (p ^ k) ∈ T.principalUnits (k + 1) := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact T.pow_prime_mem_principalUnits_succ (by omega) ih

/-- An integral unit raised to `q - 1`, for the residue cardinality `q`, has level one. -/
theorem pow_residueCardinality_sub_one_mem_principalUnits {u : F.Carrierˣ}
    (hu : T.discreteValuation (u : F.Carrier) = 1) :
    u ^ (T.residueCardinality - 1) ∈ T.principalUnits 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.finite_residueField
  let := Fintype.ofFinite T.ResidueField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have huI : (u : F.Carrier) ∈ T.Integers :=
    (T.mem_integers_iff_discreteValuation_le_one _).mpr hu.le
  let d : T.Integers := ⟨u, huI⟩
  have hd : T.residue d ≠ 0 := by
    intro h
    have h' := (IsLocalRing.residue_eq_zero_iff d).mp h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at h'
    have h2 : T.discreteValuation (u : F.Carrier) < 1 := by
      change e (ValuativeRel.valuation F.Carrier (u : F.Carrier)) < 1
      rw [← map_one e]
      exact e.strictMono h'
    rw [hu] at h2
    exact lt_irrefl _ h2
  have hpow := FiniteField.pow_card_sub_one_eq_one (T.residue d) hd
  have hmem : d ^ (T.residueCardinality - 1) - 1 ∈ IsLocalRing.maximalIdeal T.Integers := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_pow, map_one]
    change T.residue d ^ (Nat.card T.ResidueField - 1) - 1 = 0
    rw [Nat.card_eq_fintype_card, hpow, sub_self]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
  have hlt : T.discreteValuation
      (((u ^ (T.residueCardinality - 1) : F.Carrierˣ) : F.Carrier) - 1) < 1 := by
    change e (ValuativeRel.valuation F.Carrier _) < 1
    rw [← map_one e]
    apply e.strictMono
    convert hmem using 2
  refine ⟨by rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow], ?_⟩
  apply (WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).mp
  rw [← WithZero.exp_add]
  simpa using hlt

/-- The residue cardinality minus one is prime to every power of `p`. -/
theorem coprime_residueCardinality_sub_one (n : ℕ) :
    Nat.Coprime (T.residueCardinality - 1) (p ^ n) := by
  have hp : p.Prime := Fact.out
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply (Nat.Prime.coprime_iff_not_dvd hp).mpr
  intro hdvd
  rw [T.residueCardinality_eq_pow] at hdvd
  have hf := T.residueDegree_pos
  have h1 : p ∣ p ^ T.residueDegree := dvd_pow_self p hf.ne'
  have hone : 1 ≤ p ^ T.residueDegree := Nat.one_le_pow _ _ hp.pos
  have h2 := Nat.dvd_sub h1 hdvd
  rw [Nat.sub_sub_self hone] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- The unramified quasicharacter `x ↦ 2 ^ ord x`. It is continuous because it
factors through the discrete quotient by the integral units. -/
def twoPowOrdCharacter : @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI : DiscreteTopology (F.Carrierˣ ⧸ T.principalUnits 0) :=
    QuotientGroup.discreteTopology (HarmonicAnalysis.CharacterSeparation.principalUnits_isOpen T 0)
  have hker : T.principalUnits 0 ≤ T.orderHom.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (-WithZero.log (T.discreteValuation (u : F.Carrier))) = 1
    rw [hu.1]
    rfl
  let c : F.Carrierˣ ⧸ T.principalUnits 0 →* ℂˣ :=
    (zpowersHom ℂˣ (Units.mk0 2 two_ne_zero)).comp
      (QuotientGroup.lift (T.principalUnits 0) T.orderHom hker)
  exact ⟨c.comp (QuotientGroup.mk' (T.principalUnits 0)),
    (continuous_of_discreteTopology (f := ⇑c)).comp QuotientGroup.continuous_mk⟩

theorem twoPowOrdCharacter_apply (x : F.Carrierˣ) :
    T.twoPowOrdCharacter x = Units.mk0 2 two_ne_zero ^ T.ord (x : F.Carrier) :=
  rfl

theorem multiplicativeConductor_twoPowOrdCharacter :
    T.multiplicativeConductor T.twoPowOrdCharacter = 0 := by
  rw [multiplicativeConductor_eq_zero_iff]
  intro u hu
  rw [twoPowOrdCharacter_apply]
  have h0 : T.ord (u : F.Carrier) = 0 := by
    unfold ord
    rw [hu]
    rfl
  rw [h0, zpow_zero]

/-- If `2 ^ ord x` is a root of unity of `p`-power order, then `x` is an integral unit. -/
theorem discreteValuation_eq_one_of_twoPowOrd {x : F.Carrierˣ} {n : ℕ}
    (h : T.twoPowOrdCharacter x ^ (p ^ n) = 1) :
    T.discreteValuation (x : F.Carrier) = 1 := by
  rw [twoPowOrdCharacter_apply] at h
  have hn := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) h
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_pow,
    norm_zpow, Units.val_one, norm_one] at hn
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, pow_eq_one_iff_of_nonneg (zpow_nonneg (by norm_num) _) hpn,
    zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at hn
  have hx0 : T.discreteValuation (x : F.Carrier) ≠ 0 :=
    T.discreteValuation.ne_zero_iff.mpr x.ne_zero
  unfold ord at hn
  rw [← WithZero.exp_log hx0, show WithZero.log (T.discreteValuation (x : F.Carrier)) = 0 by
    omega]
  rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open CommonClosure VirtualRepresentation Weil.Local
open LocalWeil.Ramification Ramification.Padic LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

private theorem haarMeasure_nonempty' (E : Extension F) :
    Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

/-- Units of level one are zero-input approximate witnesses, for `a ≥ 0`. -/
theorem approximateWitness_zero_of_mem_principalUnits
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {a : ℝ} (ha : 0 ≤ a) (ψ : AdditiveCharacter F (baseExtension F))
    {δ : (baseExtension F).fieldˣ}
    (hδ : δ ∈ (fieldData F (baseExtension F)).principalUnits 1) :
    ApproximateWitness F eC ε 0 a ψ δ := by
  rw [approximateWitness_iff]
  intro w _ hwb _
  refine ⟨⌈a⌉₊, ?_⟩
  simp only [map_zero, value_zero hε, one_pow]
  have hpow := (fieldData F (baseExtension F)).pow_prime_pow_mem_principalUnits hδ ⌈a⌉₊
  have hlev := (fieldData F (baseExtension F)).principalUnits_antitone (Nat.le_succ _) hpow
  rw [← map_pow, fieldDeterminant_eq_one_of_mem_principalUnits F hthr hreal hinert hcmp eC he w
    ha hwb _ hlev]

/-- A zero-input approximate witness gives, for every bottom-field character of
conductor at most one, a value that is a root of unity of `p`-power order. -/
theorem exists_pow_eq_one_of_approximateWitness_zero
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {a : ℝ} (ha : 0 < a) (ψ : AdditiveCharacter F (baseExtension F))
    {δ : (baseExtension F).fieldˣ} (h : ApproximateWitness F eC ε 0 a ψ δ)
    (η : FieldCharacter F (baseExtension F))
    (hη : (fieldData F (baseExtension F)).multiplicativeConductor η ≤ 1) :
    ∃ n : ℕ, η δ ^ (p ^ n) = 1 := by
  let := (fieldData F (baseExtension F)).topology
  rw [approximateWitness_iff] at h
  obtain ⟨μ⟩ := haarMeasure_nonempty' F (baseExtension F)
  set r : ℝ := min a 1 / 2 with hr
  have hmin : 0 < min a 1 := lt_min ha one_pos
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrpos : 0 < r := by rw [hr]; linarith
  have hra : r < a := by
    rw [hr]
    linarith [min_le_left a 1]
  have hr1 : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hrpos).ne'
  have hmap := baseUpperGroup_map_reciprocityUnits F hreal hinert hcmp eC he hr0
  have hχ : ∀ w ∈ upperGroup F r, baseWeilCharacter F eC η w = 1 := by
    intro w hw
    have hmem : reciprocityUnits F eC _ (baseWeilSection F w) ∈
        (fieldData F (baseExtension F)).principalUnits ⌈r⌉₊ := by
      rw [← hmap]
      exact ⟨baseWeilSection F w, hw, rfl⟩
    exact ((fieldData F (baseExtension F)).multiplicativeTrivialAt_iff_conductor_le η 1).mpr
      hη _ ((fieldData F (baseExtension F)).principalUnits_antitone hr1 hmem)
  obtain ⟨n, hn⟩ := h (lineDifference.{uF, max uF uV} (baseWeilCharacter F eC η))
    (degree_lineDifference _) (allBreaksBelow_lineDifference _ hr0 hra hχ) μ
  refine ⟨n, ?_⟩
  simp only [map_zero, value_zero hε, one_pow] at hn
  obtain ⟨g, rfl⟩ := reciprocityUnits_surjective F eC (baseExtension F) δ
  rw [fieldDeterminant_reciprocityUnits, determinantCharacter_realizeAtBase,
    determinantCharacter_lineDifference, baseWeilCharacter_apply] at hn
  exact hn.symm

/-- Zero-input approximate witnesses lie in the units of level one, for `a > 0`.
Unramified tests force valuation zero; tame tests and the residue order `q - 1`,
prime to `p`, then force level one. -/
theorem mem_principalUnits_of_approximateWitness_zero
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {a : ℝ} (ha : 0 < a) (ψ : AdditiveCharacter F (baseExtension F))
    {δ : (baseExtension F).fieldˣ} (h : ApproximateWitness F eC ε 0 a ψ δ) :
    δ ∈ (fieldData F (baseExtension F)).principalUnits 1 := by
  let T := fieldData F (baseExtension F)
  let := T.topology
  have htest := exists_pow_eq_one_of_approximateWitness_zero F hreal hinert hcmp eC he hε ha ψ h
  have hval : T.discreteValuation (δ : (baseExtension F).field) = 1 := by
    obtain ⟨n, hn⟩ := htest T.twoPowOrdCharacter
      (by rw [T.multiplicativeConductor_twoPowOrdCharacter]; exact zero_le_one)
    exact T.discreteValuation_eq_one_of_twoPowOrd hn
  apply (PadicAbelian.mem_principalUnits_iff_bounded_characters T 1 δ).mpr
  intro η hη
  obtain ⟨n, hn⟩ := htest η hη
  have hq : η δ ^ (T.residueCardinality - 1) = 1 := by
    rw [← map_pow]
    exact (T.multiplicativeTrivialAt_iff_conductor_le η 1).mpr hη _
      (T.pow_residueCardinality_sub_one_mem_principalUnits hval)
  have hg := pow_gcd_eq_one.mpr ⟨hq, hn⟩
  rwa [(T.coprime_residueCardinality_sub_one n).gcd_eq_one, pow_one] at hg

/-- DH81 4.2 at zero input: for `a > 0`, the zero-input approximate witnesses are
exactly the units of level one of the bottom field. -/
theorem approximateWitness_zero_iff
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {a : ℝ} (ha : 0 < a) (ψ : AdditiveCharacter F (baseExtension F))
    (δ : (baseExtension F).fieldˣ) :
    ApproximateWitness F eC ε 0 a ψ δ ↔
      δ ∈ (fieldData F (baseExtension F)).principalUnits 1 :=
  ⟨mem_principalUnits_of_approximateWitness_zero F hreal hinert hcmp eC he hε ha ψ,
    approximateWitness_zero_of_mem_principalUnits F hthr hreal hinert hcmp eC he hε ha.le ψ⟩

/-- The approximate coset: relative to one approximate witness, the approximate
witnesses form precisely its coset of the units of level one. -/
theorem approximateWitness_iff_mem_coset
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (eC : ReciprocityFamily F)
    (he : GeometricWeilReciprocityRelation F F.canonicalTopologicalData
      (Correspondence.baseReciprocityCandidate F eC))
    {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    {v : LocalWeil.Lattice.{uF, max uF uV} F} {a : ℝ} (ha : 0 < a)
    {ψ : AdditiveCharacter F (baseExtension F)} {γ₀ : (baseExtension F).fieldˣ}
    (hγ₀ : ApproximateWitness F eC ε v a ψ γ₀) (γ₀' : (baseExtension F).fieldˣ) :
    ApproximateWitness F eC ε v a ψ γ₀' ↔
      γ₀' * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1 :=
  (approximateWitness_coset hε hγ₀).trans
    (approximateWitness_zero_iff F hthr hreal hinert hcmp eC he hε ha ψ _)

/-- The approximate coset clause at the index of the target, `a = minimumBreak F v hv`. -/
theorem approximateWitness_iff_mem_coset_of_isSystem
    (hthr : WeilTrivialityThresholdsNonempty.{uF, max uF uV} F)
    (hreal : AbsoluteReciprocityRealUnitImages.{uF})
    (hinert : AbsoluteUpperInertia F F.canonicalTopologicalData)
    (hcmp : UnitFiltrationComparison.{uF})
    (hgeo : CommonClosureGeometricStatement.{uF, uF})
    {eC : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hsys : IsSystem F eC ε)
    {ψ : AdditiveCharacter F (baseExtension F)}
    {v : LocalWeil.Lattice.{uF, max uF uV} F} (hv : (breakSupport F v).Nonempty)
    (hpos : PositiveBreakSupport F v) {γ₀ : (baseExtension F).fieldˣ}
    (hγ₀ : ApproximateWitness F eC ε v (minimumBreak F v hv) ψ γ₀)
    (γ₀' : (baseExtension F).fieldˣ) :
    ApproximateWitness F eC ε v (minimumBreak F v hv) ψ γ₀' ↔
      γ₀' * γ₀⁻¹ ∈ (fieldData F (baseExtension F)).principalUnits 1 :=
  approximateWitness_iff_mem_coset F hthr hreal hinert hcmp eC
    (geometric_baseReciprocityCandidate F hgeo eC hsys.1) hsys.2.1
    ((positiveBreakSupport_iff_minimumBreak_pos F v hv).mp hpos) hγ₀ γ₀'

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
