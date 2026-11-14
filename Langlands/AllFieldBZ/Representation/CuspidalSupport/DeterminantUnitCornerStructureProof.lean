import Langlands.AllFieldBZ.Group.GL.PrincipalLevelDominance
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
import Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear
open Matrix
open Topology
open MeasureTheory
universe u

/-! ### Determinants of integral and torus elements -/

section Determinant
variable {k : Type u} [Field k] [ValuativeRel k]

private theorem _root_.Langlands.GeneralLinear.prod_zpow_eq_zpow_sum' {ι H : Type*} [CommGroup H] (s : Finset ι) (f : ι → ℤ)
    (a : H) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

end Determinant
/-! ### Blockwise subgroups, dominant monoid and generators -/

section Levi
variable (k : Type u) [Field k] [ValuativeRel k] {n : ℕ} (B : BlockShape n)

variable {k B}

variable (G : Subgroup (B.Levi k))
  (hG : ∀ g : B.Levi k, g ∈ G ↔ ∀ i, ValuativeRel.valuation k (determinant (g i) : k) = 1)

end Levi
/-! ### The corner structure over a nonarchimedean local field -/

section Corner
variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k] {n : ℕ} {B : BlockShape n}
  (G : Subgroup (B.Levi k))
  (hG : ∀ g : B.Levi k, g ∈ G ↔ ∀ i, ValuativeRel.valuation k (determinant (g i) : k) = 1)
  [MeasurableSpace G] [BorelSpace G]

end Corner
end Langlands.AllFieldBZ.GeneralLinear
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding DeterminantUnitCornerStructureStatement continuous_determinantUnitInclusion determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation normalizedAbs_eq_one_iff
open Langlands.GeneralLinear
universe uF

variable {F : LocalFieldPackage.{uF}}

/-- Normalized absolute value one is valuation one. -/
theorem normalizedAbs_eq_one_iff (T : F.TopologicalData) {x : F.Carrier} (hx : x ≠ 0) :
    letI := T.valuativeRel
    T.normalizedAbs x = 1 ↔ ValuativeRel.valuation F.Carrier x = 1 := by
  let := T.valuativeRel
  have key : ∀ y : F.Carrier,
      T.normalizedAbs y ≤ 1 ↔ ValuativeRel.valuation F.Carrier y ≤ 1 := fun y =>
    (T.normalizedAbs_le_one_iff_mem_integers y).trans
      (Valuation.mem_integer_iff (ValuativeRel.valuation F.Carrier) y)
  have hmul : T.normalizedAbs x * T.normalizedAbs x⁻¹ = 1 := by
    rw [← T.normalizedAbs_mul, mul_inv_cancel₀ hx, T.normalizedAbs_one]
  have hv : ValuativeRel.valuation F.Carrier x * ValuativeRel.valuation F.Carrier x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  have hpos := T.normalizedAbs_pos hx
  constructor
  · intro h
    rw [h, one_mul] at hmul
    have h₁ := (key x).1 h.le
    have h₂ := (key x⁻¹).1 hmul.le
    refine le_antisymm h₁ ?_
    calc (1 : ValuativeRel.ValueGroupWithZero F.Carrier)
        = ValuativeRel.valuation F.Carrier x * ValuativeRel.valuation F.Carrier x⁻¹ := hv.symm
      _ ≤ ValuativeRel.valuation F.Carrier x := mul_le_of_le_one_right' h₂
  · intro h
    rw [h, one_mul] at hv
    have h₁ := (key x).2 h.le
    have h₂ := (key x⁻¹).2 hv.le
    refine le_antisymm h₁ ?_
    nlinarith [mul_le_mul_of_nonneg_left h₂ hpos.le]

/-- Membership in `G°` through the valuation of the block determinants. -/
theorem mem_determinantUnitSubgroup_iff_valuation (T : F.TopologicalData) {n : ℕ}
    (B : BlockShape n) (g : B.Levi F.Carrier) :
    letI := T.valuativeRel
    g ∈ determinantUnitSubgroup T B ↔
      ∀ i, ValuativeRel.valuation F.Carrier (determinant (g i) : F.Carrier) = 1 := by
  let := T.valuativeRel
  rw [mem_determinantUnitSubgroup_iff_normalizedAbs]
  exact forall_congr' fun i => normalizedAbs_eq_one_iff T (Units.ne_zero _)

/-- **Sandwich structure of compact-open Hecke corners of `G°`**
(Bernstein--Zelevinsky 1976, Lemma 4.9, page 39). -/
theorem determinantUnitCornerStructure : DeterminantUnitCornerStructureStatement.{uF} := by
  intro F T n B K hK
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : MeasurableSpace (determinantUnitSubgroup T B) := borel _
  have : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  exact GeneralLinear.exists_cornerStructure (determinantUnitSubgroup T B)
    (mem_determinantUnitSubgroup_iff_valuation T B) K hK

end Langlands.AllFieldBZ.CuspidalSupport
