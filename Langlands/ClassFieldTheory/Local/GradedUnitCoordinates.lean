import Langlands.ClassFieldTheory.Local.UnitFiltrationStructuralProof
import Langlands.LocalField.Normalization.Proof
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Actual residue coordinates on successive unit quotients. -/
noncomputable section
namespace Langlands.PadicField.TopologicalData
open scoped WithZero
universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The next filtration group as a subgroup of the current group. -/
def gradedUnitKernel (n : ℕ) : Subgroup (T.unitFiltration n) :=
  (T.unitFiltration (n + 1)).subgroupOf (T.unitFiltration n)

/-- Inclusion of the actual next group, using the decreasing filtration law. -/
def gradedUnitInclusion (n : ℕ) : T.unitFiltration (n + 1) →* T.unitFiltration n :=
  Subgroup.inclusion (T.unitFiltration_antitone (Nat.le_succ n))

theorem gradedUnitInclusion_range (n : ℕ) :
    (T.gradedUnitInclusion n).range = T.gradedUnitKernel n := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The actual successive quotient `U^n/U^(n+1)`, including level zero. -/
abbrev GradedUnits (n : ℕ) := T.unitFiltration n ⧸ T.gradedUnitKernel n

/-- Projection from actual field units at level `n`. -/
def gradedUnitProjection (n : ℕ) : T.unitFiltration n →* T.GradedUnits n :=
  QuotientGroup.mk' _

/-- The canonical identification of integer congruence units with field units. -/
def congruenceUnitsEquivFiltration (n : ℕ) :
    T.congruenceUnits n ≃* T.unitFiltration n :=
  (T.congruenceUnits n).equivMapOfInjective T.integerUnitsInclusion
    T.integerUnitsInclusion_injective

/-- Recover the unique integer unit underlying a filtration element. -/
def filtrationIntegerUnit (n : ℕ) : T.unitFiltration n →* T.Integersˣ :=
  (T.congruenceUnits n).subtype.comp (T.congruenceUnitsEquivFiltration n).symm.toMonoidHom

@[simp] theorem filtrationIntegerUnit_coe (n : ℕ) (x : T.unitFiltration n) :
    ((T.filtrationIntegerUnit n x : T.Integers) : F.Carrier) = (x : F.Carrierˣ) := by
  have h := congrArg (fun y : T.unitFiltration n => (y : F.Carrierˣ))
    ((T.congruenceUnitsEquivFiltration n).apply_symm_apply x)
  exact congrArg (fun y : F.Carrierˣ => (y : F.Carrier)) h

theorem filtrationIntegerUnit_mem (n : ℕ) (x : T.unitFiltration n) :
    T.filtrationIntegerUnit n x ∈ T.congruenceUnits n :=
  ((T.congruenceUnitsEquivFiltration n).symm x).property

theorem filtrationIntegerUnit_mem_iff (n m : ℕ) (x : T.unitFiltration n) :
    T.filtrationIntegerUnit n x ∈ T.congruenceUnits m ↔
      (x : F.Carrierˣ) ∈ T.unitFiltration m := by
  have he : T.integerUnitsInclusion (T.filtrationIntegerUnit n x) = x := by
    apply Units.ext
    exact T.filtrationIntegerUnit_coe n x
  constructor
  · intro h
    exact ⟨_, h, he⟩
  · rintro ⟨y, hy, hyx⟩
    have h := T.integerUnitsInclusion_injective (hyx.trans he.symm)
    simpa [← h] using hy

private theorem coordinateValuationIntegers : T.discreteValuation.Integers T.Integers := by
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

variable (π : F.Carrier) (hπ : T.ord π = 1)
include hπ

theorem coordinateUniformizer_ne_zero : π ≠ 0 := by
  intro h
  simp [h, T.ord_zero] at hπ

private theorem coordinateUniformizer_value :
    T.discreteValuation π = WithZero.exp (-1) := by
  have hv := T.discreteValuation.ne_zero_iff.mpr (T.coordinateUniformizer_ne_zero π hπ)
  have ho : WithZero.log (T.discreteValuation π) = -1 := by
    change -WithZero.log (T.discreteValuation π) = 1 at hπ
    omega
  rw [← ho, WithZero.exp_log hv]

/-- The supplied uniformizer in the actual integer ring. -/
def coordinateUniformizer : T.Integers :=
  (T.coordinateValuationIntegers.exists_of_le_one
    (r := π) (by rw [T.coordinateUniformizer_value π hπ]; norm_num)).choose

@[simp] theorem coordinateUniformizer_coe :
    (T.coordinateUniformizer π hπ : F.Carrier) = π :=
  (T.coordinateValuationIntegers.exists_of_le_one
    (r := π) (by rw [T.coordinateUniformizer_value π hπ]; norm_num)).choose_spec

theorem maximalIdeal_eq_span_coordinateUniformizer :
    IsLocalRing.maximalIdeal T.Integers = Ideal.span {T.coordinateUniformizer π hπ} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit x ↔ x ∈ Ideal.span {T.coordinateUniformizer π hπ}
  rw [T.coordinateValuationIntegers.isUnit_iff_valuation_eq_one]
  rw [← SetLike.mem_coe,
    T.coordinateValuationIntegers.coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  change T.discreteValuation x.val ≠ 1 ↔
    T.discreteValuation x.val ≤ T.discreteValuation (T.coordinateUniformizer π hπ).val
  rw [T.coordinateUniformizer_coe, T.coordinateUniformizer_value π hπ]
  have hle := T.coordinateValuationIntegers.map_le_one x
  have hstep : T.discreteValuation x.val < 1 ↔
      T.discreteValuation x.val ≤ WithZero.exp (-1) := by
    simpa [← WithZero.exp_add] using
      (WithZero.lt_mul_exp_iff_le (x := T.discreteValuation x.val)
        (y := WithZero.exp (-1)) WithZero.exp_ne_zero)
  rw [← hstep]
  exact ⟨fun h => lt_of_le_of_ne hle h, fun h => h.ne⟩

theorem mem_maximalIdeal_pow_iff_coordinate_dvd (n : ℕ) (a : T.Integers) :
    a ∈ IsLocalRing.maximalIdeal T.Integers ^ n ↔
      T.coordinateUniformizer π hπ ^ n ∣ a := by
  rw [T.maximalIdeal_eq_span_coordinateUniformizer π hπ,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- Integrality of the literal field quotient, with no order assigned to a zero numerator. -/
theorem unitCoefficient_integral (n : ℕ) (x : T.unitFiltration n) :
    (((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n ∈ T.Integers := by
  have hx := (T.mem_congruenceUnits_iff n _).mp (T.filtrationIntegerUnit_mem n x)
  obtain ⟨a, ha⟩ := (T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ n _).mp hx
  have he := congrArg (fun b : T.Integers => (b : F.Carrier)) ha
  change ((T.filtrationIntegerUnit n x : T.Integers) : F.Carrier) - 1 =
    (T.coordinateUniformizer π hπ : F.Carrier) ^ n * (a : F.Carrier) at he
  rw [T.filtrationIntegerUnit_coe, T.coordinateUniformizer_coe] at he
  rw [he, mul_div_cancel_left₀ _ (pow_ne_zero _ (T.coordinateUniformizer_ne_zero π hπ))]
  exact a.property

/-- The integral coefficient `(x-1)/π^n`. At `x=1` it is zero, also at level zero. -/
def unitCoefficient (n : ℕ) (x : T.unitFiltration n) : T.Integers :=
  ⟨(((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n,
    T.unitCoefficient_integral π hπ n x⟩

@[simp] theorem unitCoefficient_coe (n : ℕ) (x : T.unitFiltration n) :
    (T.unitCoefficient π hπ n x : F.Carrier) =
      (((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n := rfl

@[simp] theorem unitCoefficient_one (n : ℕ) : T.unitCoefficient π hπ n 1 = 0 := by
  apply Subtype.ext
  simp [unitCoefficient]

theorem coordinateUniformizer_integer_ne_zero : T.coordinateUniformizer π hπ ≠ 0 := by
  intro h
  have he := congrArg (fun a : T.Integers => (a : F.Carrier)) h
  exact T.coordinateUniformizer_ne_zero π hπ (by simpa using he)

theorem coordinateUniformizer_pow_mul_coefficient (n : ℕ) (x : T.unitFiltration n) :
    T.coordinateUniformizer π hπ ^ n * T.unitCoefficient π hπ n x =
      (T.filtrationIntegerUnit n x : T.Integers) - 1 := by
  apply Subtype.ext
  change (T.coordinateUniformizer π hπ : F.Carrier) ^ n *
    (T.unitCoefficient π hπ n x : F.Carrier) =
      ((T.filtrationIntegerUnit n x : T.Integers) : F.Carrier) - 1
  rw [T.coordinateUniformizer_coe, T.unitCoefficient_coe, T.filtrationIntegerUnit_coe]
  exact mul_div_cancel₀ _ (pow_ne_zero _ (T.coordinateUniformizer_ne_zero π hπ))

theorem unitCoefficient_mul (n : ℕ) (x y : T.unitFiltration n) :
    T.unitCoefficient π hπ n (x * y) =
      T.unitCoefficient π hπ n x + T.unitCoefficient π hπ n y +
        T.coordinateUniformizer π hπ ^ n *
          T.unitCoefficient π hπ n x * T.unitCoefficient π hπ n y := by
  apply Subtype.ext
  change ((((x : F.Carrierˣ) : F.Carrier) * ((y : F.Carrierˣ) : F.Carrier)) - 1) / π ^ n =
    ((((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n) +
    ((((y : F.Carrierˣ) : F.Carrier) - 1) / π ^ n) +
    (T.coordinateUniformizer π hπ : F.Carrier) ^ n *
    ((((x : F.Carrierˣ) : F.Carrier) - 1) / π ^ n) *
    ((((y : F.Carrierˣ) : F.Carrier) - 1) / π ^ n)
  rw [T.coordinateUniformizer_coe]
  field_simp
  ring

@[simp] theorem residue_coordinateUniformizer : T.residue (T.coordinateUniformizer π hπ) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, T.maximalIdeal_eq_span_coordinateUniformizer π hπ]
  exact Ideal.mem_span_singleton_self _

/-- The residue coefficient vanishes precisely on the next filtration group. -/
theorem residue_unitCoefficient_eq_zero_iff (n : ℕ) (x : T.unitFiltration n) :
    T.residue (T.unitCoefficient π hπ n x) = 0 ↔
      (x : F.Carrierˣ) ∈ T.unitFiltration (n + 1) := by
  rw [IsLocalRing.residue_eq_zero_iff, T.maximalIdeal_eq_span_coordinateUniformizer π hπ,
    Ideal.mem_span_singleton, ← T.filtrationIntegerUnit_mem_iff n (n + 1) x,
    T.mem_congruenceUnits_iff, T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ,
    ← T.coordinateUniformizer_pow_mul_coefficient π hπ n x, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero _ (T.coordinateUniformizer_integer_ne_zero π hπ))]

/-- Positive-level reduction of the actual coefficient, written multiplicatively. -/
def positiveUnitCoordinate (n : ℕ) (hn : 0 < n) :
    T.unitFiltration n →* Multiplicative T.ResidueField where
  toFun x := Multiplicative.ofAdd (T.residue (T.unitCoefficient π hπ n x))
  map_one' := by simp
  map_mul' x y := by
    change T.residue (T.unitCoefficient π hπ n (x * y)) =
      T.residue (T.unitCoefficient π hπ n x) + T.residue (T.unitCoefficient π hπ n y)
    rw [T.unitCoefficient_mul π hπ]
    simp [hn.ne']

@[simp] theorem positiveUnitCoordinate_apply (n : ℕ) (hn : 0 < n)
    (x : T.unitFiltration n) :
    T.positiveUnitCoordinate π hπ n hn x =
      Multiplicative.ofAdd (T.residue (T.unitCoefficient π hπ n x)) := rfl

theorem positiveUnitCoordinate_ker (n : ℕ) (hn : 0 < n) :
    (T.positiveUnitCoordinate π hπ n hn).ker = T.gradedUnitKernel n := by
  ext x
  change T.residue (T.unitCoefficient π hπ n x) = 0 ↔
    (x : F.Carrierˣ) ∈ T.unitFiltration (n + 1)
  exact T.residue_unitCoefficient_eq_zero_iff π hπ n x

/-- Every residue coefficient is obtained from the unit `1 + π^n a`. -/
theorem positiveUnitCoordinate_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (T.positiveUnitCoordinate π hπ n hn) := by
  intro z
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := T.Integers) z.toAdd
  let b : T.Integers := 1 + T.coordinateUniformizer π hπ ^ n * a
  have hb : T.residue b = 1 := by simp [b, hn.ne']
  have hu : IsUnit b := (IsLocalRing.residue_ne_zero_iff_isUnit b).mp (by rw [hb]; exact one_ne_zero)
  have hmem : hu.unit ∈ T.congruenceUnits n := by
    rw [T.mem_congruenceUnits_iff, hu.unit_spec,
      T.mem_maximalIdeal_pow_iff_coordinate_dvd π hπ]
    exact ⟨a, by dsimp [b]; ring⟩
  let x : T.unitFiltration n := T.congruenceUnitsEquivFiltration n ⟨hu.unit, hmem⟩
  have hx : T.filtrationIntegerUnit n x = hu.unit := by
    exact congrArg (fun v : T.congruenceUnits n => (v : T.Integersˣ))
      ((T.congruenceUnitsEquivFiltration n).symm_apply_apply ⟨hu.unit, hmem⟩)
  have hc : T.unitCoefficient π hπ n x = a := by
    apply mul_left_cancel₀ (pow_ne_zero n (T.coordinateUniformizer_integer_ne_zero π hπ))
    rw [T.coordinateUniformizer_pow_mul_coefficient π hπ, hx, hu.unit_spec]
    dsimp [b]
    ring
  refine ⟨x, ?_⟩
  change Multiplicative.ofAdd (T.residue (T.unitCoefficient π hπ n x)) = z
  rw [hc, ha]
  rfl

/-- The induced positive-level equivalence, using the supplied uniformizer. -/
def gradedUnitsPositiveEquiv (n : ℕ) (hn : 0 < n) :
    T.GradedUnits n ≃* Multiplicative T.ResidueField :=
  (QuotientGroup.quotientMulEquivOfEq (T.positiveUnitCoordinate_ker π hπ n hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (T.positiveUnitCoordinate_surjective π hπ n hn))

/-- Computation on the quotient class of an actual filtration unit. -/
@[simp] theorem gradedUnitsPositiveEquiv_projection (n : ℕ) (hn : 0 < n)
    (x : T.unitFiltration n) :
    T.gradedUnitsPositiveEquiv π hπ n hn (T.gradedUnitProjection n x) =
      Multiplicative.ofAdd (T.residue (T.unitCoefficient π hπ n x)) := rfl

omit hπ

/-- At level zero the coordinate is reduction of the underlying integer unit. -/
def zeroUnitCoordinate : T.unitFiltration 0 →* T.ResidueFieldˣ :=
  T.residueUnits.comp (T.filtrationIntegerUnit 0)

@[simp] theorem zeroUnitCoordinate_apply (x : T.unitFiltration 0) :
    T.zeroUnitCoordinate x = T.residueUnits (T.filtrationIntegerUnit 0 x) := rfl

@[simp] theorem zeroUnitCoordinate_val (x : T.unitFiltration 0) :
    (T.zeroUnitCoordinate x : T.ResidueField) =
      T.residue (T.filtrationIntegerUnit 0 x : T.Integers) := rfl

theorem zeroUnitCoordinate_ker : T.zeroUnitCoordinate.ker = T.gradedUnitKernel 0 := by
  ext x
  change T.residueUnits (T.filtrationIntegerUnit 0 x) = 1 ↔
    (x : F.Carrierˣ) ∈ T.unitFiltration (0 + 1)
  rw [← Units.val_inj]
  change T.residue (T.filtrationIntegerUnit 0 x : T.Integers) = T.residue 1 ↔ _
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  rw [← T.filtrationIntegerUnit_mem_iff, T.mem_congruenceUnits_iff, pow_one]

theorem zeroUnitCoordinate_surjective : Function.Surjective T.zeroUnitCoordinate := by
  intro z
  obtain ⟨a, ha⟩ := IsLocalRing.surjective_units_map_of_local_ringHom T.residue
    IsLocalRing.residue_surjective inferInstance z
  have hm : a ∈ T.congruenceUnits 0 := by rw [T.congruenceUnits_zero]; trivial
  refine ⟨T.congruenceUnitsEquivFiltration 0 ⟨a, hm⟩, ?_⟩
  change T.residueUnits
    (((T.congruenceUnitsEquivFiltration 0).symm
      (T.congruenceUnitsEquivFiltration 0 ⟨a, hm⟩)) : T.Integersˣ) = z
  simpa [residueUnits] using ha

/-- The canonical multiplicative residue-unit equivalence at level zero. -/
def gradedUnitsZeroEquiv : T.GradedUnits 0 ≃* T.ResidueFieldˣ :=
  (QuotientGroup.quotientMulEquivOfEq T.zeroUnitCoordinate_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ T.zeroUnitCoordinate_surjective)

@[simp] theorem gradedUnitsZeroEquiv_projection (x : T.unitFiltration 0) :
    T.gradedUnitsZeroEquiv (T.gradedUnitProjection 0 x) =
      T.residueUnits (T.filtrationIntegerUnit 0 x) := rfl

end Langlands.PadicField.TopologicalData
