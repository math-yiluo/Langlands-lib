import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Langlands.LinearAlgebra.RootDatumNegation
import Mathlib.LinearAlgebra.RootSystem.WeylGroup
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Negation is not Weyl in simply connected type A of rank at least two -/

noncomputable section

namespace Langlands.TypeANegationWeyl

/-- A type-A Cartan entry split into its diagonal and two neighboring entries. -/
theorem cartan_entry {n : ℕ} (a i : Fin n) :
    CartanMatrix.A n a i = (if i = a then 2 else 0) -
      (if i.val + 1 = a.val then 1 else 0) -
      (if a.val + 1 = i.val then 1 else 0) := by
  simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The weighted sum over the predecessor of a vertex. -/
theorem sum_predecessor {n : ℕ} (a : Fin n) :
    (∑ i : Fin n, if i.val + 1 = a.val then (i.val + 1 : ℤ) else 0) = a.val := by
  classical
  by_cases ha : a.val = 0
  · simp [ha]
  · let p : Fin n := ⟨a.val - 1, by omega⟩
    have hp (i : Fin n) : i.val + 1 = a.val ↔ i = p := by
      simp only [Fin.ext_iff, p]
      omega
    simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    dsimp [p]
    omega

/-- The weighted sum over the successor of a vertex. -/
theorem sum_successor {n : ℕ} (a : Fin n) :
    (∑ i : Fin n, if a.val + 1 = i.val then (i.val + 1 : ℤ) else 0) =
      if a.val + 1 < n then a.val + 2 else 0 := by
  classical
  by_cases ha : a.val + 1 < n
  · let p : Fin n := ⟨a.val + 1, ha⟩
    have hp (i : Fin n) : a.val + 1 = i.val ↔ i = p := by
      simp only [Fin.ext_iff, p]
      omega
    simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ha]
    dsimp [p]
    ring
  · have hp (i : Fin n) : ¬ a.val + 1 = i.val := by omega
    simp [hp, ha]

/-- Numbering the simple coroots by 1 through n kills every Cartan row modulo n+1. -/
theorem weighted_cartan_sum {n : ℕ} (a : Fin n) :
    (∑ i : Fin n, (i.val + 1 : ℤ) * CartanMatrix.A n a i) =
      if a.val + 1 = n then n + 1 else 0 := by
  classical
  simp only [cartan_entry, mul_sub, mul_ite, mul_zero, mul_one,
    Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ a), sum_predecessor, sum_successor]
  split_ifs <;> push_cast <;> omega

section RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) {n : ℕ} (e : b.support ≃ Fin n)

/-- An additive residue of a weight, evaluated on the numbered simple coroots. -/
def residue : X →+ ZMod (n + 1) where
  toFun x := ∑ i : Fin n, (i.val + 1 : ZMod (n + 1)) *
    (P.toLinearMap x (P.coroot (e.symm i).val) : ℤ)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]

variable (hA : ∀ a c : b.support,
  P.pairing a.val c.val = CartanMatrix.A n (e a) (e c))

include hA in
/-- The residue vanishes on every simple root. -/
theorem residue_simple (a : b.support) : residue P b e (P.root a.val) = 0 := by
  change (∑ i : Fin n, (i.val + 1 : ZMod (n + 1)) *
    (P.toLinearMap (P.root a.val) (P.coroot (e.symm i).val) : ℤ)) = 0
  simp only [P.root_coroot_eq_pairing, hA, Equiv.apply_symm_apply]
  have h := congrArg (fun z : ℤ => (z : ZMod (n + 1))) (weighted_cartan_sum (e a))
  push_cast at h
  rw [h]
  split_ifs <;> simp

include hA in
/-- The residue vanishes on every root. -/
theorem residue_root (a : J) : residue P b e (P.root a) = 0 := by
  classical
  obtain ⟨c, -, -, hc⟩ := b.exists_root_eq_sum_int a
  rw [hc, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_zsmul, residue_simple P b e hA ⟨i, hi⟩, smul_zero]

include hA in
/-- Every integral Weyl element preserves the residue of every weight. -/
theorem residue_weyl (w : P.Aut) (hw : w ∈ P.weylGroup) (x : X) :
    residue P b e (w.weightEquiv x) = residue P b e x := by
  induction hw using RootPairing.weylGroup.induction generalizing x with
  | mem i =>
    change residue P b e (P.reflection i x) = _
    rw [P.reflection_apply, map_sub, map_zsmul, residue_root P b e hA, smul_zero, sub_zero]
  | one => rfl
  | mul a c ha hc ia ic =>
    change residue P b e (a.weightEquiv (c.weightEquiv x)) = _
    rw [ia, ic]

/-- The first fundamental weight, constructed on the full integral lattice. -/
def firstWeight (hspan : P.corootSpan ℤ = ⊤) (hn : 0 < n) : X :=
  P.toLinearMap.toPerfPair.symm
    ((IntegralWeylVector.corootBasis P b hspan).constr ℤ
      (fun a => if e a = (⟨0, hn⟩ : Fin n) then 1 else 0))

@[simp] theorem pairing_firstWeight (hspan : P.corootSpan ℤ = ⊤) (hn : 0 < n)
    (a : b.support) :
    P.toLinearMap (firstWeight P b e hspan hn) (P.coroot a.val) =
      if e a = (⟨0, hn⟩ : Fin n) then 1 else 0 := by
  unfold firstWeight
  rw [LinearMap.apply_symm_toPerfPair_self,
    ← IntegralWeylVector.corootBasis_apply P b hspan a, Module.Basis.constr_basis]

/-- Its residue is one. -/
theorem residue_firstWeight (hspan : P.corootSpan ℤ = ⊤) (hn : 0 < n) :
    residue P b e (firstWeight P b e hspan hn) = 1 := by
  classical
  change (∑ i : Fin n, (i.val + 1 : ZMod (n + 1)) *
    (P.toLinearMap (firstWeight P b e hspan hn) (P.coroot (e.symm i).val) : ℤ)) = 1
  simp [pairing_firstWeight, mul_ite]

include hA in
/-- Minus identity is not an integral Weyl automorphism in simply connected A_n, n≥2. -/
theorem negAut_not_mem_weylGroup (hspan : P.corootSpan ℤ = ⊤) (hn : 2 ≤ n) :
    RootDatumNegation.negAut P ∉ P.weylGroup := by
  intro hw
  have h := residue_weyl P b e hA _ hw (firstWeight P b e hspan (by omega))
  change residue P b e (-(firstWeight P b e hspan _)) = _ at h
  rw [map_neg, residue_firstWeight] at h
  have := ZMod.neg_one_eq_one_iff.mp h
  omega

end RootDatum

end Langlands.TypeANegationWeyl
