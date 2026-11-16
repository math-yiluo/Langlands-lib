import Langlands.LinearAlgebra.TypeANegationWeyl

/-! # Negation is not Weyl in simply connected type E6 -/

noncomputable section

namespace Langlands.TypeE6NegationWeyl

/-- An integral vector in the Cartan kernel modulo three. -/
def weights : Fin 6 → ℤ := ![1, 0, 2, 0, 1, 2]

theorem weighted_cartan_sum (a : Fin 6) :
    (∑ i : Fin 6, (weights i : ZMod 3) * (CartanMatrix.E 6 a i : ℤ)) = 0 := by
  have h : ∀ a : Fin 6,
      (∑ i : Fin 6, (weights i : ZMod 3) * (CartanMatrix.E 6 a i : ℤ)) = 0 := by
    decide
  exact h a

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base) (e : b.support ≃ Fin 6)

/-- The residue of a weight evaluated on the six actual simple coroots. -/
def residue : X →+ ZMod 3 where
  toFun x := ∑ i : Fin 6, (weights i : ZMod 3) *
    (P.toLinearMap x (P.coroot (e.symm i).val) : ℤ)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

variable (hE : ∀ a c : b.support,
  P.pairing a.val c.val = CartanMatrix.E 6 (e a) (e c))

include hE in
/-- Every actual simple root has zero residue. -/
theorem residue_simple (a : b.support) : residue P b e (P.root a.val) = 0 := by
  change (∑ i : Fin 6, (weights i : ZMod 3) *
    (P.toLinearMap (P.root a.val) (P.coroot (e.symm i).val) : ℤ)) = 0
  simp only [P.root_coroot_eq_pairing, hE, Equiv.apply_symm_apply]
  exact weighted_cartan_sum (e a)

include hE in
/-- Every actual root has zero residue. -/
theorem residue_root (a : J) : residue P b e (P.root a) = 0 := by
  classical
  obtain ⟨c, -, -, hc⟩ := b.exists_root_eq_sum_int a
  rw [hc, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, residue_simple P b e hE ⟨i, hi⟩, smul_zero]

include hE in
/-- The full integral Weyl group preserves the residue of every weight. -/
theorem residue_weyl (w : P.Aut) (hw : w ∈ P.weylGroup) (x : X) :
    residue P b e (w.weightEquiv x) = residue P b e x := by
  induction hw using RootPairing.weylGroup.induction generalizing x with
  | mem i =>
    change residue P b e (P.reflection i x) = _
    rw [P.reflection_apply, map_sub, map_zsmul, residue_root P b e hE,
      smul_zero, sub_zero]
  | one => rfl
  | mul a c ha hc ia ic =>
    change residue P b e (a.weightEquiv (c.weightEquiv x)) = _
    rw [ia, ic]

/-- The first fundamental weight has residue one. -/
theorem residue_firstWeight (hspan : P.corootSpan ℤ = ⊤) :
    residue P b e (TypeANegationWeyl.firstWeight P b e hspan (by decide)) = 1 := by
  classical
  change (∑ i : Fin 6, (weights i : ZMod 3) *
    (P.toLinearMap (TypeANegationWeyl.firstWeight P b e hspan (by decide))
      (P.coroot (e.symm i).val) : ℤ)) = 1
  simp [TypeANegationWeyl.pairing_firstWeight, mul_ite, weights]

include hE in
/-- Negation cannot belong to the integral Weyl group when simple coroots span. -/
theorem negAut_not_mem_weylGroup (hspan : P.corootSpan ℤ = ⊤) :
    RootDatumNegation.negAut P ∉ P.weylGroup := by
  intro hw
  have h := residue_weyl P b e hE _ hw
    (TypeANegationWeyl.firstWeight P b e hspan (by decide))
  change residue P b e (-(TypeANegationWeyl.firstWeight P b e hspan _)) = _ at h
  rw [map_neg, residue_firstWeight] at h
  exact (show (-1 : ZMod 3) ≠ 1 by decide) h

end Langlands.TypeE6NegationWeyl
