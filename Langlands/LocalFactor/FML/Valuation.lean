import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# FML normalized valuation and filtration definitions

Adapted by Worker 20 from Fukuhiro Ueda, epsilon_FML, commit
0b4159be50e1bd45ddff1de4280399576a3e2024 (Apache-2.0).
Modifications: targeted imports, project namespace, explicit universe, exposed
normalizing valuation, and only the constructors and their supporting laws.
See Valuation.md and LICENSE for provenance and the retained license.
-/

namespace Langlands.FML

universe u

open scoped WithZero

section Construction

/-- The canonical multiplicative valuation, normalized in `ℤᵐ⁰` by Mathlib's local-field
value-group equivalence.  This is an implementation detail of `ord`. -/
noncomputable def normalizedMultiplicativeValuation
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : Valuation F ℤᵐ⁰ :=
  (ValuativeRel.valuation F).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMulEquiv.toMonoidWithZeroHom
    (fun _ _ h ↦ (map_le_map_iff
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)).2 h)

/-- Negative logarithm on the nonzero part of `ℤᵐ⁰`, with zero sent to infinity. -/
private def multiplicativeToAdditiveOrder (a : ℤᵐ⁰) : WithTop ℤ :=
  if a = 0 then ⊤ else ((-WithZero.log a : ℤ) : WithTop ℤ)

private lemma multiplicativeToAdditiveOrder_mul (a b : ℤᵐ⁰) :
    multiplicativeToAdditiveOrder (a * b) =
      multiplicativeToAdditiveOrder a + multiplicativeToAdditiveOrder b := by
  by_cases ha : a = 0
  · simp [ha, multiplicativeToAdditiveOrder]
  by_cases hb : b = 0
  · simp [hb, multiplicativeToAdditiveOrder]
  simp [multiplicativeToAdditiveOrder, ha, hb, WithZero.log_mul, add_comm]

private lemma multiplicativeToAdditiveOrder_le_iff (a b : ℤᵐ⁰) :
    multiplicativeToAdditiveOrder a ≤ multiplicativeToAdditiveOrder b ↔ b ≤ a := by
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [multiplicativeToAdditiveOrder]
    · simp [multiplicativeToAdditiveOrder, hb]
  by_cases hb : b = 0
  · subst b
    simp [multiplicativeToAdditiveOrder, ha]
  simp only [multiplicativeToAdditiveOrder, ite_eq_right ha, ite_eq_right hb, WithTop.coe_le_coe]
  rw [neg_le_neg_iff, WithZero.log_le_log hb ha]

private lemma min_multiplicativeToAdditiveOrder_le {a b c : ℤᵐ⁰}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : c ≤ max a b) :
    min (multiplicativeToAdditiveOrder a) (multiplicativeToAdditiveOrder b) ≤
      multiplicativeToAdditiveOrder c := by
  simp only [multiplicativeToAdditiveOrder, ite_eq_right ha, ite_eq_right hb, ite_eq_right hc,
    ← WithTop.coe_min, WithTop.coe_le_coe]
  rcases (le_max_iff.mp h) with hca | hcb
  · have hlog : WithZero.log c ≤ WithZero.log a :=
      (WithZero.log_le_log hc ha).2 hca
    omega
  · have hlog : WithZero.log c ≤ WithZero.log b :=
      (WithZero.log_le_log hc hb).2 hcb
    omega

/-- The normalized integer-valued additive order on a nonarchimedean local field.

It is bundled as an `AddValuation`, so it can be used as a function `F → WithTop ℤ` while its
zero, product, and ultrametric laws remain available through Mathlib's valuation API. -/
noncomputable def ord (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : AddValuation F (WithTop ℤ) :=
  AddValuation.of
    (fun x ↦ multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F x))
    (by simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation])
    (by simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation])
    (fun x y ↦ by
      by_cases hx : x = 0
      · subst x
        simp
      by_cases hy : y = 0
      · subst y
        simp
      by_cases hxy : x + y = 0
      · rw [hxy]
        simp [multiplicativeToAdditiveOrder, normalizedMultiplicativeValuation]
      exact min_multiplicativeToAdditiveOrder_le
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hx)
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hy)
        ((normalizedMultiplicativeValuation F).ne_zero_iff.mpr hxy)
        ((normalizedMultiplicativeValuation F).map_add x y))
    (fun x y ↦ by
      rw [(normalizedMultiplicativeValuation F).map_mul]
      exact multiplicativeToAdditiveOrder_mul _ _)

end Construction

section OrderAPI

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

@[simp]
theorem ord_zero : ord F 0 = ⊤ := (ord F).map_zero

@[simp]
theorem ord_one : ord F 1 = 0 := (ord F).map_one

@[simp]
theorem ord_eq_top_iff {x : F} : ord F x = ⊤ ↔ x = 0 := (ord F).top_iff

@[simp]
theorem ord_ne_top_iff {x : F} : ord F x ≠ ⊤ ↔ x ≠ 0 := (ord F).ne_top_iff

@[simp]
theorem ord_neg (x : F) : ord F (-x) = ord F x := (ord F).map_neg x

@[simp]
theorem ord_mul (x y : F) : ord F (x * y) = ord F x + ord F y :=
  (ord F).map_mul x y

/-- The nonarchimedean triangle inequality in order notation. -/
theorem ord_add (x y : F) : min (ord F x) (ord F y) ≤ ord F (x + y) :=
  (ord F).map_add x y

/-- Comparison by `ord` is the reverse of Mathlib's canonical valuative relation. -/
theorem ord_le_ord_iff (x y : F) : ord F x ≤ ord F y ↔ y ≤ᵥ x := by
  change multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F x) ≤
      multiplicativeToAdditiveOrder (normalizedMultiplicativeValuation F y) ↔ _
  rw [multiplicativeToAdditiveOrder_le_iff]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F y) ≤
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F x) ↔ _
  rw [map_le_map_iff]
  exact (Valuation.Compatible.vle_iff_le y x).symm

/-- Strict comparison by `ord` is the reverse strict valuative relation. -/
theorem ord_lt_ord_iff (x y : F) : ord F x < ord F y ↔ y <ᵥ x := by
  rw [lt_iff_not_ge, ord_le_ord_iff]
  rfl

/-- Nonnegative order is membership in the valuation subring. -/
theorem ord_nonneg_iff_mem_integer (x : F) :
    0 ≤ ord F x ↔ x ∈ (ValuativeRel.valuation F).integer := by
  calc
    0 ≤ ord F x ↔ ord F 1 ≤ ord F x := by simp
    _ ↔ x ≤ᵥ (1 : F) := ord_le_ord_iff F 1 x
    _ ↔ ValuativeRel.valuation F x ≤ ValuativeRel.valuation F 1 :=
      Valuation.Compatible.vle_iff_le x 1
    _ ↔ ValuativeRel.valuation F x ≤ 1 := by simp
    _ ↔ x ∈ (ValuativeRel.valuation F).integer :=
      (Valuation.mem_integer_iff (ValuativeRel.valuation F) x).symm


end OrderAPI


section Lattices

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The canonical valuation ring, used as the scalar ring of the lattices. -/
noncomputable abbrev ringOfIntegers : Subring F :=
  (ValuativeRel.valuation F).integer

/-- The fractional lattice of elements of order at least `n`. -/
noncomputable def lattice (n : ℤ) : Submodule (ringOfIntegers F) F where
  carrier := {x | (n : WithTop ℤ) ≤ ord F x}
  zero_mem' := by simp
  add_mem' {x y} hx hy := (ord F).map_le_add hx hy
  smul_mem' a x hx := by
    change (n : WithTop ℤ) ≤ ord F ((a : F) * x)
    rw [ord_mul]
    have ha : 0 ≤ ord F (a : F) :=
      (ord_nonneg_iff_mem_integer F a).2 a.property
    simpa only [zero_add] using add_le_add ha hx

@[simp] theorem mem_lattice {n : ℤ} {x : F} :
    x ∈ lattice F n ↔ (n : WithTop ℤ) ≤ ord F x := Iff.rfl

/-- The unit group of the canonical valuation subring, inside the field units. -/
noncomputable abbrev unitGroup : Subgroup Fˣ :=
  (ValuativeRel.valuation F).valuationSubring.unitGroup

/-- Integral units have order zero. -/
theorem ord_unitGroup (u : Fˣ) (hu : u ∈ unitGroup F) : ord F (u : F) = 0 := by
  have hv : ValuativeRel.valuation F (u : F) = 1 :=
    by
      simpa only [unitGroup, Valuation.mem_unitGroup_iff] using hu
  change multiplicativeToAdditiveOrder
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F (u : F))) = 0
  simp [hv, multiplicativeToAdditiveOrder]

/-- The positive principal-unit layer as an actual subgroup. -/
private noncomputable def positiveUnitFiltration (n : ℕ) : Subgroup Fˣ where
  carrier := {u | u ∈ unitGroup F ∧
    (((n + 1 : ℕ) : ℤ) : WithTop ℤ) ≤ ord F ((u : F) - 1)}
  one_mem' := ⟨(unitGroup F).one_mem, by simp⟩
  mul_mem' := by
    rintro u v ⟨hu0, hu⟩ ⟨hv0, hv⟩
    refine ⟨(unitGroup F).mul_mem hu0 hv0, ?_⟩
    change _ ≤ ord F ((u : F) * v - 1)
    rw [show (u : F) * v - 1 = u * ((v : F) - 1) + ((u : F) - 1) by ring]
    apply (ord F).map_le_add _ hu
    simpa [ord_mul, ord_unitGroup F u hu0] using hv
  inv_mem' := by
    rintro u ⟨hu0, hu⟩
    refine ⟨(unitGroup F).inv_mem hu0, ?_⟩
    simp only [Units.val_inv_eq_inv_val]
    rw [show (u : F)⁻¹ - 1 = -((u : F) - 1) * (u : F)⁻¹ by
      field_simp
      ring]
    simpa only [ord_mul, ord_neg, AddValuation.map_inv, ord_unitGroup F u hu0,
      neg_zero, add_zero] using hu

/-- `U⁰ = Oˣ`; the positive layers impose congruence to one at that depth. -/
noncomputable def unitFiltration : ℕ → Subgroup Fˣ
  | 0 => unitGroup F
  | n + 1 => positiveUnitFiltration F n

@[simp] theorem unitFiltration_zero : unitFiltration F 0 = unitGroup F := rfl

/-- The positive layer retains the integral-unit condition explicitly. -/
theorem mem_unitFiltration_succ (n : ℕ) (u : Fˣ) :
    u ∈ unitFiltration F (n + 1) ↔ u ∈ unitGroup F ∧
      (u : F) - 1 ∈ lattice F ((n + 1 : ℕ) : ℤ) := Iff.rfl

end Lattices

end Langlands.FML
