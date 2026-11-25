import Langlands.ClassFieldTheory.Global.LocalPowerIndex
import Langlands.ClassFieldTheory.Local.LocalFieldOrder
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# `n`-th powers in a nonarchimedean local field

For a nonarchimedean local field `K` and `n` invertible in `K`, the subgroup `Kˣⁿ` of `n`-th powers
is open and of finite index in `Kˣ`. Both follow from Hensel's lemma in the form
`exists_one_add_mul_mul_pow_eq` (every element of `1 + n² c 𝒪` with `c ∈ 𝓂` is an `n`-th power) and
the decomposition `x = π^{ord x} · u` with `u` a unit of `𝒪[K]` (`unitPart`, from the Library's
normalized order and uniformizer).
-/

noncomputable section

namespace Langlands.GaloisCohomology.Local

open ValuativeRel IsLocalRing ClassFieldTheory.Local

universe u

variable {K : Type u} [Field K] [ValuativeRel K]

/-- A unit of `K` of valuation one, as a unit of `𝒪[K]`. -/
def integerUnitOfValuationEqOne (x : Kˣ) (hx : valuation K (x : K) = 1) : 𝒪[K]ˣ where
  val := ⟨x, by rw [Valuation.mem_integer_iff, hx]⟩
  inv := ⟨((x⁻¹ : Kˣ) : K), by
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

@[simp]
theorem coe_integerUnitOfValuationEqOne (x : Kˣ) (hx : valuation K (x : K) = 1) :
    (((integerUnitOfValuationEqOne x hx : 𝒪[K]ˣ) : 𝒪[K]) : K) = x :=
  rfl

variable (K) in
/-- The inclusion `𝒪[K]ˣ → Kˣ`. -/
abbrev integerUnitsMap : 𝒪[K]ˣ →* Kˣ :=
  Units.map ((𝒪[K]).subtype : 𝒪[K] →+* K).toMonoidHom

@[simp]
theorem coe_integerUnitsMap_apply (w : 𝒪[K]ˣ) :
    ((integerUnitsMap K w : Kˣ) : K) = ((w : 𝒪[K]) : K) :=
  rfl

theorem integerUnitsMap_injective : Function.Injective (integerUnitsMap K) := fun _ _ h =>
  Units.ext (Subtype.ext (congrArg Units.val h))

theorem valuation_integerUnitsMap (w : 𝒪[K]ˣ) : valuation K ((integerUnitsMap K w : Kˣ) : K) = 1 :=
  (Valuation.integer.integers _).one_of_isUnit w.isUnit

variable (K) in
/-- The units of `𝒪[K]` congruent to `1` modulo an ideal `I`. -/
def integerCongruenceUnits (I : Ideal 𝒪[K]) : Subgroup 𝒪[K]ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker

theorem mem_integerCongruenceUnits_iff (I : Ideal 𝒪[K]) (w : 𝒪[K]ˣ) :
    w ∈ integerCongruenceUnits K I ↔ (w : 𝒪[K]) - 1 ∈ I := by
  rw [integerCongruenceUnits, MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
  rfl

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in
/-- The ring of integers of a nonarchimedean local field is `𝓂`-adically complete. -/
theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem valuation_unit_mul_zpow_neg_eq_one (x : Kˣ) :
    valuation K ((x * localUniformizer K ^ (-normalizedUnitOrder K (.ofMul x)) : Kˣ) : K) = 1 := by
  rw [← normalizedUnitOrder_eq_zero_iff]
  change normalizedUnitOrder K (.ofMul x + .ofMul (localUniformizer K ^
    (-normalizedUnitOrder K (.ofMul x)))) = 0
  rw [map_add, ofMul_zpow, map_zsmul, normalizedUnitOrder_localUniformizer]
  simp

variable (K) in
/-- The unit part `x · π^{-ord x}` of a unit `x` of `K`, for the Library's normalized order and
uniformizer `π = localUniformizer K`. -/
def unitPart : Kˣ →* 𝒪[K]ˣ where
  toFun x := integerUnitOfValuationEqOne _ (valuation_unit_mul_zpow_neg_eq_one x)
  map_one' := Units.ext (Subtype.ext (by simp))
  map_mul' x y := Units.ext (Subtype.ext (by
    simp only [coe_integerUnitOfValuationEqOne, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Subring.coe_mul]
    rw [show (Additive.ofMul (x * y)) = .ofMul x + .ofMul y from rfl, map_add, neg_add,
      zpow_add₀ (Units.ne_zero _)]
    ring))

theorem integerUnitsMap_unitPart_mul (x : Kˣ) :
    integerUnitsMap K (unitPart K x) * localUniformizer K ^ normalizedUnitOrder K (.ofMul x) = x := by
  apply Units.ext
  change ((x * localUniformizer K ^ (-normalizedUnitOrder K (.ofMul x)) : Kˣ) : K) *
    ((localUniformizer K ^ normalizedUnitOrder K (.ofMul x) : Kˣ) : K) = x
  rw [← Units.val_mul, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem finite_quotient_integer {I : Ideal 𝒪[K]} (hI : I ≠ ⊥) : Finite (𝒪[K] ⧸ I) := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal 𝒪[K]
    (IsPrincipalIdealRing.principal _) I hI
  exact IsLocalRing.finite_quotient_iff.mpr ⟨n, hn.ge⟩

theorem integerCongruenceUnits_finiteIndex {I : Ideal 𝒪[K]} (hI : I ≠ ⊥) :
    (integerCongruenceUnits K I).FiniteIndex := by
  have := finite_quotient_integer hI
  exact Subgroup.finiteIndex_ker _

/-- Hensel's lemma for `n`-th powers: a unit congruent to `1` modulo `n² c` with `c ∈ 𝓂` is an
`n`-th power of a unit. -/
theorem integerCongruenceUnits_le_range_pow {n : ℕ} (hn : n ≠ 0) {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) :
    integerCongruenceUnits K (Ideal.span {(n : 𝒪[K]) ^ 2 * c}) ≤
      (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range := by
  intro w hw
  rw [mem_integerCongruenceUnits_iff, Ideal.mem_span_singleton'] at hw
  obtain ⟨t, ht⟩ := hw
  have := isAdicComplete_integer K
  obtain ⟨z, hz⟩ := ClassFieldTheory.Global.exists_one_add_mul_mul_pow_eq 𝓂[K] n hn c hc t
  have hw' : (1 + (n : 𝒪[K]) * c * z) ^ n = w := by
    rw [hz, mul_comm _ t, ht, add_sub_cancel]
  have hunit : IsUnit (1 + (n : 𝒪[K]) * c * z) :=
    (isUnit_pow_iff hn).mp (hw' ▸ w.isUnit)
  exact ⟨hunit.unit, Units.ext (by simpa using hw')⟩

/-- The uniformizer `π = localUniformizer K`, as an element of `𝒪[K]`. -/
def integerUniformizer : 𝒪[K] :=
  ⟨localUniformizer K, (Valuation.mem_integer_iff _ _).mpr ((Valuation.vle_one_iff _).mp
    ((normalizedUnitOrder_nonneg_iff K _).mp
      (by rw [normalizedUnitOrder_localUniformizer]; exact zero_le_one)))⟩

theorem integerUniformizer_mem_maximalIdeal : (integerUniformizer : 𝒪[K]) ∈ 𝓂[K] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h1 := (Valuation.integer.integers (valuation K)).one_of_isUnit h
  have h2 := (normalizedUnitOrder_eq_zero_iff K (localUniformizer K)).mpr h1
  rw [normalizedUnitOrder_localUniformizer] at h2
  exact one_ne_zero h2

theorem integerUniformizer_ne_zero : (integerUniformizer : 𝒪[K]) ≠ 0 := fun h =>
  (localUniformizer K).ne_zero (congrArg Subtype.val h)

/-- The ideal `(n² π)` of `𝒪[K]` used for the `n`-th powers. -/
def powerCongruenceIdeal (n : ℕ) : Ideal 𝒪[K] :=
  Ideal.span {(n : 𝒪[K]) ^ 2 * integerUniformizer}

theorem powerCongruenceIdeal_ne_bot {n : ℕ} (hn : (n : K) ≠ 0) :
    (powerCongruenceIdeal n : Ideal 𝒪[K]) ≠ ⊥ := by
  rw [powerCongruenceIdeal, Ne, Ideal.span_singleton_eq_bot]
  refine mul_ne_zero (pow_ne_zero 2 fun h => hn ?_) integerUniformizer_ne_zero
  have := congrArg Subtype.val h
  simpa using this

theorem integerUnitsMap_mem_range_pow {n : ℕ} (hn : n ≠ 0) {w : 𝒪[K]ˣ}
    (hw : w ∈ integerCongruenceUnits K (powerCongruenceIdeal n)) :
    integerUnitsMap K w ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  obtain ⟨v, rfl⟩ := integerCongruenceUnits_le_range_pow hn integerUniformizer_mem_maximalIdeal hw
  exact ⟨integerUnitsMap K v, by simp⟩

variable (K) in
/-- The homomorphism `x ↦ (ord x mod n, class of the unit part of x mod n² π)`. Its kernel consists
of `n`-th powers. -/
def powerTestHom (n : ℕ) : Kˣ →* Multiplicative (ZMod n) × (𝒪[K] ⧸ powerCongruenceIdeal n)ˣ :=
  MonoidHom.prod
    ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))).comp
      (AddMonoidHom.toMultiplicativeRight (normalizedUnitOrder K)))
    ((Units.map (Ideal.Quotient.mk _).toMonoidHom).comp (unitPart K))

theorem ker_powerTestHom_le {n : ℕ} (hn : n ≠ 0) :
    (powerTestHom K n).ker ≤ (powMonoidHom n : Kˣ →* Kˣ).range := by
  intro x hx
  rw [MonoidHom.mem_ker, Prod.ext_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  have hord : (n : ℤ) ∣ normalizedUnitOrder K (.ofMul x) := by
    have : ((normalizedUnitOrder K (.ofMul x) : ℤ) : ZMod n) = 0 := congrArg Multiplicative.toAdd h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp this
  obtain ⟨m, hm⟩ := hord
  have hu : unitPart K x ∈ integerCongruenceUnits K (powerCongruenceIdeal n) := h2
  obtain ⟨y, hy⟩ := integerUnitsMap_mem_range_pow hn hu
  refine ⟨y * localUniformizer K ^ m, ?_⟩
  change (y * localUniformizer K ^ m) ^ n = x
  rw [mul_pow, ← zpow_natCast (localUniformizer K ^ m), ← zpow_mul, mul_comm m, ← hm]
  change y ^ n * _ = x
  rw [show y ^ n = integerUnitsMap K (unitPart K x) from hy, integerUnitsMap_unitPart_mul]

/-- For `n` invertible in `K`, the `n`-th powers have finite index in `Kˣ`. -/
theorem finiteIndex_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    ((powMonoidHom n : Kˣ →* Kˣ).range).FiniteIndex := by
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have : NeZero n := ⟨hn0⟩
  have := finite_quotient_integer (powerCongruenceIdeal_ne_bot hn)
  have : (powerTestHom K n).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_powerTestHom_le hn0)

/-- For `n` invertible in `K`, `Kˣ / Kˣⁿ` is finite. -/
theorem finite_quotient_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := by
  have := finiteIndex_range_powMonoidHom hn
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The image in `Kˣ` of the units congruent to `1` modulo `(c)`, for `0 ≠ c ∈ 𝓂`, is open. -/
theorem isOpen_map_integerCongruenceUnits {c : 𝒪[K]} (hc : c ∈ 𝓂[K]) (hc0 : c ≠ 0) :
    IsOpen (((integerCongruenceUnits K (Ideal.span {c})).map (integerUnitsMap K) : Subgroup Kˣ) :
      Set Kˣ) := by
  have hcK : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hlt : valuation K (c : K) < 1 := by
    by_contra h
    have h1 : valuation K (c : K) = 1 := le_antisymm c.2 (not_lt.mp h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hc
      ((Valuation.integer.integers (valuation K)).isUnit_of_one (isUnit_iff_ne_zero.mpr hcK)
        (by exact h1))
  let T : Set K := (fun t => 1 + (c : K) * t) '' (𝒪[K] : Set K)
  have hT : IsOpen T := by
    let e := (Homeomorph.mulLeft₀ (c : K) hcK).trans (Homeomorph.addLeft (1 : K))
    have h := e.isOpenMap _ (Valuation.isOpen_integer (v := valuation K))
    convert h using 1
    ext y
    simp [T, e]
  convert hT.preimage Units.continuous_val using 1
  ext x
  simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, T]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_integerCongruenceUnits_iff, Ideal.mem_span_singleton'] at hw
    obtain ⟨t, ht⟩ := hw
    refine ⟨t, t.2, ?_⟩
    have ht' : (t : K) * (c : K) = ((w : 𝒪[K]) : K) - 1 := congrArg Subtype.val ht
    rw [coe_integerUnitsMap_apply]
    linear_combination ht'
  · rintro ⟨t, ht, hx⟩
    have hv : valuation K (x : K) = 1 := by
      rw [← hx]
      apply Valuation.map_one_add_of_lt
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp ht)) hlt
    refine ⟨integerUnitOfValuationEqOne x hv, ?_, Units.ext rfl⟩
    rw [mem_integerCongruenceUnits_iff, Ideal.mem_span_singleton']
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    show t * (c : K) = (x : K) - 1
    rw [← hx]
    ring

/-- For `n` invertible in `K`, the `n`-th powers form an open subgroup of `Kˣ`. -/
theorem isOpen_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have hc : (n : 𝒪[K]) ^ 2 * integerUniformizer ∈ 𝓂[K] :=
    Ideal.mul_mem_left _ _ integerUniformizer_mem_maximalIdeal
  have hc0 : (n : 𝒪[K]) ^ 2 * integerUniformizer ≠ 0 := by
    have := powerCongruenceIdeal_ne_bot hn
    rwa [powerCongruenceIdeal, Ne, Ideal.span_singleton_eq_bot] at this
  refine Subgroup.isOpen_mono ?_ (isOpen_map_integerCongruenceUnits hc hc0)
  rintro _ ⟨w, hw, rfl⟩
  exact integerUnitsMap_mem_range_pow hn0 hw

end Langlands.GaloisCohomology.Local
