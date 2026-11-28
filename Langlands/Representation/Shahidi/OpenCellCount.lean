import Langlands.Representation.Shahidi.OpenCellValue

/-! # Counting classes of bounded depth

The classes `Y ∈ M_(a×b)(K) / M_(a×b)(𝒪)` with `ϖ^D Y` integral number at most `q^(a b D)`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear

universe u

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

local instance ocCountTopologicalSpace : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocCountValuativeRel : ValuativeRel K.Carrier := K.canonicalTopologicalData.valuativeRel
local instance ocCountIsNonarchimedeanLocalField : IsNonarchimedeanLocalField K.Carrier := K.canonicalTopologicalData.localField

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
  (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

/-- A section of the residue map. -/
def residueLift : K.canonicalTopologicalData.ResidueField → K.canonicalTopologicalData.Integers :=
  Function.surjInv (IsLocalRing.residue_surjective)

theorem residue_residueLift (d : K.canonicalTopologicalData.ResidueField) :
    IsLocalRing.residue _ (residueLift K d) = d :=
  Function.surjInv_eq _ d

include hϖ in
/-- An integer with residue zero is divisible by `ϖ`. -/
theorem div_uniformizer_mem_of_residue_eq_zero {x : K.canonicalTopologicalData.Integers}
    (hx : IsLocalRing.residue _ x = 0) :
    (x : K.Carrier) * ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) ∈
      K.canonicalTopologicalData.Integers := by
  set v := ValuativeRel.valuation K.Carrier
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  by_cases h0 : (x : K.Carrier) = 0
  · rw [h0, zero_mul]
    exact zero_mem _
  have hlt : v (x : K.Carrier) < 1 := by
    have hle : v (x : K.Carrier) ≤ 1 := x.2
    refine lt_of_le_of_ne hle fun heq => hx ?_
    exact (Valuation.integer.integers v).isUnit_iff_valuation_eq_one.mpr heq
  obtain ⟨k, hk⟩ := hϖ.2 _ h0
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have : v (x : K.Carrier) ≥ 1 := by
      rw [hk]
      exact one_le_zpow_of_nonpos₀ (Iwasawa.valuation_pos v ϖ) hϖ.1.le (by omega)
    exact absurd hlt (not_lt.2 this)
  change v ((x : K.Carrier) * ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier)) ≤ 1
  rw [map_mul, hk, Units.val_inv_eq_inv_val, map_inv₀, ← zpow_neg_one, ← zpow_add₀
    (Iwasawa.valuation_pos v ϖ).ne']
  exact zpow_le_one₀ (Iwasawa.valuation_pos v ϖ) hϖ.1.le (by omega)

/-- The value of the digits `d` at the uniformizer: `∑_i lift(d_i) ϖ^(-(i+1))`. -/
def digitValue {D : ℕ} (d : Fin D → K.canonicalTopologicalData.ResidueField) : K.Carrier :=
  ∑ i : Fin D, (residueLift K (d i) : K.Carrier) * ((ϖ ^ (-((i : ℤ) + 1)) : K.Carrierˣ) : K.Carrier)

include hϖ in
/-- Every `y` with `ϖ^D y` integral differs from a digit value by an integer. -/
theorem exists_digitValue (D : ℕ) (y : K.Carrier)
    (hy : ((ϖ ^ (D : ℤ) : K.Carrierˣ) : K.Carrier) * y ∈ K.canonicalTopologicalData.Integers) :
    ∃ d : Fin D → K.canonicalTopologicalData.ResidueField,
      y - digitValue K (ϖ := ϖ) d ∈ K.canonicalTopologicalData.Integers := by
  induction D generalizing y with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    simpa [digitValue] using hy
  | succ D ih =>
    set z : K.canonicalTopologicalData.Integers := ⟨_, hy⟩
    set d₀ := IsLocalRing.residue _ z
    set w : K.Carrier := y - (residueLift K d₀ : K.Carrier) *
      ((ϖ ^ (-((D : ℤ) + 1)) : K.Carrierˣ) : K.Carrier)
    have hres : IsLocalRing.residue _ (z - residueLift K d₀) = 0 := by
      rw [map_sub, residue_residueLift, sub_self]
    have hw : ((ϖ ^ (D : ℤ) : K.Carrierˣ) : K.Carrier) * w ∈
        K.canonicalTopologicalData.Integers := by
      have h := div_uniformizer_mem_of_residue_eq_zero K hϖ hres
      have hπ : (ϖ : K.Carrier) ≠ 0 := ϖ.ne_zero
      have heq : ((z - residueLift K d₀ : K.canonicalTopologicalData.Integers) : K.Carrier) *
          ((ϖ⁻¹ : K.Carrierˣ) : K.Carrier) = ((ϖ ^ (D : ℤ) : K.Carrierˣ) : K.Carrier) * w := by
        simp only [w, z, AddSubgroupClass.coe_sub, Units.val_zpow_eq_zpow_val,
          Units.val_inv_eq_inv_val]
        rw [show (((D + 1 : ℕ) : ℤ)) = (D : ℤ) + 1 by push_cast; ring, zpow_add₀ hπ, zpow_neg,
          zpow_add₀ hπ, zpow_one, zpow_natCast]
        field_simp
      rwa [heq] at h
    obtain ⟨d', hd'⟩ := ih w hw
    refine ⟨Fin.snoc d' d₀, ?_⟩
    convert hd' using 1
    simp only [digitValue, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_castSucc, Fin.val_last, w]
    ring

variable (a b : ℕ)

/-- The classes of the matrices given by digits. -/
def digitClass {D : ℕ} (d : Fin a → Fin b → Fin D → K.canonicalTopologicalData.ResidueField) :
    Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b :=
  QuotientAddGroup.mk (Matrix.of fun i j => digitValue K (ϖ := ϖ) (d i j))

theorem mem_integralMatrices_iff (Y : Matrix (Fin a) (Fin b) K.Carrier) :
    Y ∈ integralMatrices K a b ↔ ∀ i j, Y i j ∈ K.canonicalTopologicalData.Integers := by
  constructor
  · intro h i j
    exact h i (Set.mem_univ _) j (Set.mem_univ _)
  · intro h i _ j _
    exact h i j

include hϖ in
theorem mk_mem_range_digitClass {D : ℕ} (Y : Matrix (Fin a) (Fin b) K.Carrier)
    (hY : ∀ i j, ((ϖ ^ (D : ℤ) : K.Carrierˣ) : K.Carrier) * Y i j ∈
      K.canonicalTopologicalData.Integers) :
    (QuotientAddGroup.mk Y : Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) ∈
      Set.range (digitClass K (ϖ := ϖ) a b (D := D)) := by
  choose d hd using fun i j => exists_digitValue K hϖ D (Y i j) (hY i j)
  refine ⟨d, ?_⟩
  rw [digitClass, QuotientAddGroup.eq, mem_integralMatrices_iff]
  intro i j
  simpa [sub_eq_neg_add] using hd i j

include hϖ in
/-- The classes `Y` with `ϖ^D Y` integral form a finite set of at most `q^(a b D)`
elements. -/
theorem finite_and_ncard_le {D : ℕ}
    (S : Set (Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b))
    (hS : ∀ y ∈ S, ∀ i j, ((ϖ ^ (D : ℤ) : K.Carrierˣ) : K.Carrier) *
      (Quotient.out y : Matrix (Fin a) (Fin b) K.Carrier) i j ∈
        K.canonicalTopologicalData.Integers) :
    S.Finite ∧ S.ncard ≤ K.canonicalTopologicalData.residueCardinality ^ (a * b * D) := by
  have := K.canonicalTopologicalData.finite_residueField
  have hsub : S ⊆ Set.range (digitClass K (ϖ := ϖ) a b (D := D)) := by
    intro y hy
    have h := mk_mem_range_digitClass K hϖ a b (Quotient.out y) (hS y hy)
    have hmk : (QuotientAddGroup.mk (Quotient.out y) :
        Matrix (Fin a) (Fin b) K.Carrier ⧸ integralMatrices K a b) = y := Quotient.out_eq y
    rwa [hmk] at h
  have hfin : (Set.range (digitClass K (ϖ := ϖ) a b (D := D))).Finite := Set.finite_range _
  refine ⟨hfin.subset hsub, ?_⟩
  calc S.ncard ≤ (Set.range (digitClass K (ϖ := ϖ) a b (D := D))).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ (Set.univ : Set (Fin a → Fin b → Fin D → K.canonicalTopologicalData.ResidueField)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le Set.finite_univ
    _ = K.canonicalTopologicalData.residueCardinality ^ (a * b * D) := by
        rw [Set.ncard_univ]
        simp only [Nat.card_fun, Nat.card_fin]
        rw [← pow_mul, ← pow_mul]
        rw [show D * (b * a) = a * b * D by ring]
        rfl

end Langlands.Shahidi.OpenCell
