import Langlands.Shimura.Unitary.CentralExchangeSplitting
import Mathlib.Algebra.Algebra.Opposite

/-! # The opposite-algebra similitudes and translations in Harris's Appendix -/

noncomputable section
universe u v

namespace Langlands.FormalGroup.Harris
open MulOpposite Langlands.Shimura

variable (k : Type u) (B : Type v) [CommRing k] [Ring B] [Algebra k B]

/-- The actual involution exchanging the factors of the opposite-algebra product. -/
def splitInvolution : AlgebraInvolution k (Bᵐᵒᵖ × B) where
  linear :=
    { toFun x := (op x.2, unop x.1)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one := rfl
  map_mul _ _ := rfl
  involutive _ := rfl

@[simp]
theorem splitInvolution_apply (x : Bᵐᵒᵖ × B) :
    splitInvolution k B x = (op x.2, unop x.1) := rfl

private def firstFactor :
    AlgebraInvolution.CentralExchangeSplitting (splitInvolution k B) Bᵐᵒᵖ where
  idempotent := (1, 0)
  idempotent_mul_self := Prod.ext (one_mul _) (zero_mul _)
  idempotent_mul_comm x := by
    apply Prod.ext <;> simp
  involution_idempotent := by
    apply Prod.ext <;> simp
  projection := RingHom.fst _ _
  lift x := (x, 0)
  lift_mul _ _ := Prod.ext rfl (zero_mul _).symm
  projection_lift _ := rfl
  lift_projection x := Prod.ext (one_mul _).symm (zero_mul _).symm

/-- A split similitude is determined by its opposite-algebra component and scalar multiplier. -/
def splitSimilitudeCoordinates :
    (splitInvolution k B).similitudes ≃* (Bᵐᵒᵖ)ˣ × kˣ :=
  (firstFactor k B).similitudesEquiv

@[simp]
theorem splitSimilitudeCoordinates_fst (g : (splitInvolution k B).similitudes) :
    ((splitSimilitudeCoordinates k B g).1 : Bᵐᵒᵖ) =
      ((g.val.1 : Bᵐᵒᵖ × B)).1 := rfl

@[simp]
theorem splitSimilitudeCoordinates_snd (g : (splitInvolution k B).similitudes) :
    (splitSimilitudeCoordinates k B g).2 = (splitInvolution k B).multiplier g := rfl

/-- The actual similitude with the given opposite component and multiplier. -/
def splitSimilitudeElement (d : (Bᵐᵒᵖ)ˣ) (e : kˣ) : (splitInvolution k B).similitudes :=
  (splitSimilitudeCoordinates k B).symm (d, e)

@[simp]
theorem splitSimilitudeElement_multiplier (d : (Bᵐᵒᵖ)ˣ) (e : kˣ) :
    (splitInvolution k B).multiplier (splitSimilitudeElement k B d e) = e :=
  (firstFactor k B).similitudesEquiv_symm_multiplier (d, e)

theorem splitSimilitudeElement_val (d : (Bᵐᵒᵖ)ˣ) (e : kˣ) :
    ((splitSimilitudeElement k B d e).val.1 : Bᵐᵒᵖ × B) =
      ((d : Bᵐᵒᵖ), algebraMap k B (e : k) * unop (↑d⁻¹ : Bᵐᵒᵖ)) := by
  change (((firstFactor k B).similitudesEquiv.symm (d, e)).val.1 : Bᵐᵒᵖ × B) = _
  rw [AlgebraInvolution.CentralExchangeSplitting.similitudesEquiv_symm_val]
  change (d.val, (0 : B)) + (e : k) • ((0 : Bᵐᵒᵖ), unop (↑d⁻¹ : Bᵐᵒᵖ)) = _
  apply Prod.ext
  · change d.val + (e : k) • (0 : Bᵐᵒᵖ) = d.val
    rw [smul_zero, add_zero]
  · change 0 + (e : k) • unop (↑d⁻¹ : Bᵐᵒᵖ) = _
    rw [zero_add, Algebra.smul_def]

/-- The split pair satisfies the scalar product equation in the original algebra. -/
theorem splitSimilitude_pair_equation (g : (splitInvolution k B).similitudes) :
    unop ((g.val.1 : Bᵐᵒᵖ × B)).1 * ((g.val.1 : Bᵐᵒᵖ × B)).2 =
      algebraMap k B ((splitInvolution k B).multiplier g : k) := by
  obtain ⟨⟨d, e⟩, rfl⟩ := (splitSimilitudeCoordinates k B).symm.surjective g
  change unop (((splitSimilitudeElement k B d e).val.1 : Bᵐᵒᵖ × B)).1 *
      (((splitSimilitudeElement k B d e).val.1 : Bᵐᵒᵖ × B)).2 =
    algebraMap k B ((splitInvolution k B).multiplier (splitSimilitudeElement k B d e) : k)
  rw [splitSimilitudeElement_val, splitSimilitudeElement_multiplier]
  change unop (d : Bᵐᵒᵖ) * (algebraMap k B (e : k) * unop (↑d⁻¹ : Bᵐᵒᵖ)) = _
  rw [← mul_assoc, ← Algebra.commutes, mul_assoc]
  have hinv : unop (d : Bᵐᵒᵖ) * unop (↑d⁻¹ : Bᵐᵒᵖ) = 1 := by
    rw [← unop_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, unop_one]
  rw [hinv, mul_one]

/-- The split similitude whose right translation gives the component shift of (A.3). -/
def weilComponentElement (uniformizer : (Bᵐᵒᵖ)ˣ) (p : kˣ) (f : ℕ) :
    (splitInvolution k B).similitudes :=
  splitSimilitudeElement k B uniformizer (p ^ f)

theorem right_mul_weilComponentElement (g : (splitInvolution k B).similitudes)
    (uniformizer : (Bᵐᵒᵖ)ˣ) (p : kˣ) (f : ℕ) :
    ((g * weilComponentElement k B uniformizer p f).val.1 : Bᵐᵒᵖ × B) =
      (((g.val.1 : Bᵐᵒᵖ × B)).1 * (uniformizer : Bᵐᵒᵖ),
        ((g.val.1 : Bᵐᵒᵖ × B)).2 * algebraMap k B ((p ^ f : kˣ) : k) *
          unop (↑uniformizer⁻¹ : Bᵐᵒᵖ)) := by
  change (g.val.1 : Bᵐᵒᵖ × B) *
    (splitSimilitudeElement k B uniformizer (p ^ f)).val.1.val = _
  rw [splitSimilitudeElement_val]
  apply Prod.ext
  · rfl
  · exact (mul_assoc _ _ _).symm

/-- The determinant correction in (A.6) uses the negative determinant order in the first factor. -/
def determinantComponentElement (uniformizer : (Bᵐᵒᵖ)ˣ) (detOrder : ℤ) :
    (splitInvolution k B).similitudes :=
  splitSimilitudeElement k B (uniformizer ^ (-detOrder)) 1

theorem right_mul_determinantComponentElement (g : (splitInvolution k B).similitudes)
    (uniformizer : (Bᵐᵒᵖ)ˣ) (detOrder : ℤ) :
    ((g * determinantComponentElement k B uniformizer detOrder).val.1 : Bᵐᵒᵖ × B) =
      (((g.val.1 : Bᵐᵒᵖ × B)).1 * (↑(uniformizer ^ (-detOrder)) : Bᵐᵒᵖ),
        ((g.val.1 : Bᵐᵒᵖ × B)).2 * unop (↑(uniformizer ^ detOrder) : Bᵐᵒᵖ)) := by
  change (g.val.1 : Bᵐᵒᵖ × B) *
    (splitSimilitudeElement k B (uniformizer ^ (-detOrder)) 1).val.1.val = _
  rw [splitSimilitudeElement_val, Units.val_one, map_one, one_mul, zpow_neg, inv_inv]
  rfl

end Langlands.FormalGroup.Harris
