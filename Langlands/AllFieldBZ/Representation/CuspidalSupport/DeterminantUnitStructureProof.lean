import Langlands.AllFieldBZ.Group.GL.UnramifiedCharacter
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding continuous_determinantUnitInclusion determinantUnitInclusion determinantUnitInclusion_apply determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnit_sup_center_finiteIndex isOpen_determinantUnitSubgroup leviDeterminantNorm leviDeterminantNorm_apply mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs
open Langlands.GeneralLinear
universe uF

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

private def _root_.Langlands.CuspidalSupport.leviOrderMod : B.Levi F.Carrier →*
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

private theorem _root_.Langlands.CuspidalSupport.ord_det_scalar_uniformizer (m : ℕ) (k : ℤ) :
    T.ord (determinant (scalar (n := m) (T.uniformizerUnit ^ k)) : F.Carrier) =
      (m : ℤ) * k := by
  change T.ord (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin m) (T.uniformizerUnit ^ k)) : F.Carrier) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_pow_eq_pow_val,
    ← zpow_natCast, T.ord_zpow, Units.val_zpow_eq_zpow_val, T.uniformizerUnit_val,
    T.ord_zpow, T.ord_uniformizer, mul_one]

private theorem _root_.Langlands.CuspidalSupport.ker_leviOrderMod_le :
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

end Langlands.AllFieldBZ.CuspidalSupport
