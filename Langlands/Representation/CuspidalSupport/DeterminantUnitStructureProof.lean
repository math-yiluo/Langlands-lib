import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
import Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
import Langlands.Group.GL.UnramifiedCharacter
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The actual determinant-unit quotient is commutative. -/
theorem determinantUnitQuotient_mul_comm
    (x y : B.Levi F.Carrier ⧸ determinantUnitSubgroup T B) : x * y = y * x := by
  let e := QuotientGroup.quotientKerEquivRange (leviDeterminantNorm T B)
  exact e.injective ((e.map_mul x y).trans
    ((mul_comm (e x) (e y)).trans (e.map_mul y x).symm))

private def leviOrderMod : B.Levi F.Carrier →*
    (∀ i : Fin B.length, Multiplicative (ZMod (B.size i))) where
  toFun g i := Multiplicative.ofAdd (T.ord (determinant (g i) : F.Carrier) : ZMod (B.size i))
  map_one' := by
    funext i
    change Multiplicative.ofAdd (T.ord (determinant (1 : GeneralLinear (B.size i) F.Carrier) : F.Carrier) : ZMod (B.size i)) = 1
    simp [T.ord_one]
  map_mul' g h := by
    funext i
    change Multiplicative.ofAdd
      (T.ord (determinant (g i * h i) : F.Carrier) : ZMod (B.size i)) = _
    simp only [map_mul, Units.val_mul, T.ord_mul (determinant (g i)).ne_zero
      (determinant (h i)).ne_zero, Int.cast_add]
    rfl

private theorem ord_det_scalar_uniformizer (m : ℕ) (k : ℤ) :
    T.ord (determinant (scalar (n := m) (T.uniformizerUnit ^ k)) : F.Carrier) =
      (m : ℤ) * k := by
  change T.ord (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin m) (T.uniformizerUnit ^ k)) : F.Carrier) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val,
    ← zpow_natCast, T.ord_zpow, Units.val_zpow_eq_zpow_val, T.uniformizerUnit_val,
    T.ord_zpow, T.ord_uniformizer, mul_one]

private theorem ker_leviOrderMod_le :
    (leviOrderMod T B).ker ≤ determinantUnitSubgroup T B ⊔
      Subgroup.center (B.Levi F.Carrier) := by
  intro g hg
  have hd (i : Fin B.length) : (B.size i : ℤ) ∣ T.ord (determinant (g i) : F.Carrier) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    exact congrArg Multiplicative.toAdd (congrFun hg i)
  choose k hk using hd
  let z : B.Levi F.Carrier := fun i => scalar (T.uniformizerUnit ^ k i)
  have hz : z ∈ Subgroup.center (B.Levi F.Carrier) := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    funext i
    exact (Matrix.GeneralLinearGroup.scalar_commute (T.uniformizerUnit ^ k i) (a i)).symm
  have hgz : g * z⁻¹ ∈ determinantUnitSubgroup T B := by
    rw [mem_determinantUnitSubgroup_iff_normalizedAbs]
    intro i
    apply (T.ord_eq_zero_iff_normalizedAbs _).mp
    change T.ord (determinant (g i * (z i)⁻¹) : F.Carrier) = 0
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [T.ord_mul (determinant (g i)).ne_zero (inv_ne_zero (determinant (z i)).ne_zero),
      T.ord_inv]
    rw [show T.ord (determinant (z i) : F.Carrier) = (B.size i : ℤ) * k i from
      ord_det_scalar_uniformizer T (B.size i) (k i), hk i, add_neg_cancel]
  simpa only [inv_mul_cancel_right] using Subgroup.mul_mem_sup hgz hz

/-- Determinant orders modulo the positive block sizes give a finite quotient
whose kernel is contained in the determinant-unit subgroup joined with the center. -/
theorem determinantUnit_sup_center_finiteIndex :
    (determinantUnitSubgroup T B ⊔ Subgroup.center (B.Levi F.Carrier)).FiniteIndex := by
  let (i : Fin B.length) : NeZero (B.size i) := ⟨(B.positive i).ne'⟩
  let : Finite (∀ i : Fin B.length, Multiplicative (ZMod (B.size i))) := inferInstance
  exact Subgroup.finiteIndex_of_le (ker_leviOrderMod_le T B)

/-- BZ76 §3.20(a)-(b): quotient commutativity, finite index after adjoining
the center, and compactness of the determinant-unit central intersection. -/
theorem leviDeterminantUnitStructure (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) :
    LeviDeterminantUnitStructureTheorem F T B := by
  let := T.topology
  exact ⟨determinantUnitQuotient_mul_comm T B,
    determinantUnit_sup_center_finiteIndex T B,
    leviDeterminantUnitCentralCompactness F T B⟩

end Langlands.CuspidalSupport
