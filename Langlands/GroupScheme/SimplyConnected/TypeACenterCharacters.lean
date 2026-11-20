import Langlands.GroupScheme.SimplyConnected.CenterCharacterCartan
import Langlands.GroupScheme.SimplyConnected.TypeARankOneOrbit
import Langlands.LinearAlgebra.ClassicalCartanDeterminants

/-! # The cyclic centre characters and sign action in type A -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

private theorem typeA_predecessor_sum {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j.val + 1 = i.val then (j.val : ℤ) + 1 else 0) = i.val := by
  by_cases hi : i.val = 0
  · simp [hi]
  · let j : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hj : j.val + 1 = i.val := by dsimp [j]; omega
    rw [Finset.sum_eq_single j]
    · simp [hj, show (j.val : ℤ) + 1 = i.val by omega]
    · intro a _ ha
      exact ite_eq_right (fun h => ha (Fin.ext (by omega)))
    · simp

private theorem typeA_successor_sum {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if i.val + 1 = j.val then (j.val : ℤ) + 1 else 0) =
      if i.val + 1 < n then (i.val : ℤ) + 2 else 0 := by
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hi⟩
    rw [ite_eq_left hi, Finset.sum_eq_single j]
    · simp [j]; ring
    · intro a _ ha
      exact ite_eq_right (fun h => ha (Fin.ext h.symm))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (by have := j.isLt; omega)

private theorem typeA_row_integral {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, CartanMatrix.A n i j * ((j.val : ℤ) + 1)) =
      if i.val + 1 < n then 0 else (n : ℤ) + 1 := by
  classical
  have h (j : Fin n) :
      CartanMatrix.A n i j * ((j.val : ℤ) + 1) =
        (if i = j then 2 * ((i.val : ℤ) + 1) else 0) -
        (if j.val + 1 = i.val then (j.val : ℤ) + 1 else 0) -
        (if i.val + 1 = j.val then (j.val : ℤ) + 1 else 0) := by
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> simp_all
    omega
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    typeA_predecessor_sum, typeA_successor_sum, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i)]
  have := i.isLt
  split_ifs <;> omega

private theorem typeA_row_cyclic {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, CartanMatrix.A n i j • (((j.val : ℤ) + 1 : ℤ) : ZMod (n + 1))) = 0 := by
  have h := congrArg (fun x : ℤ => (x : ZMod (n + 1))) (typeA_row_integral i)
  change (((∑ j : Fin n, CartanMatrix.A n i j * ((j.val : ℤ) + 1)) : ℤ) :
      ZMod (n + 1)) = _ at h
  simp only [Int.cast_sum, Int.cast_mul, ← smul_eq_mul (α := ZMod (n + 1)),
    Int.cast_smul_eq_zsmul] at h
  refine h.trans ?_
  split_ifs
  · exact Int.cast_zero
  · simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using ZMod.natCast_self' n

namespace TitsIndexData

open Langlands.LinearAlgebra

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)
local notation "C" => characterLattice (Functor.obj (BC) d.toralCenter.group)

variable (hsc : IsSimplyConnected G) {n : ℕ} (e : d.Vertex ≃ Fin n)
  (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))

include hA in
private theorem centerCharacterTypeA_relations (a : d.Vertex) :
    ∑ b, d.cartan a b • (((((e b).val : ℤ) + 1) : ℤ) : ZMod (n + 1)) = 0 := by
  simp_rw [hA]
  let f (i : Fin n) : ZMod (n + 1) :=
    CartanMatrix.A n (e a) i • (((i.val : ℤ) + 1 : ℤ) : ZMod (n + 1))
  change (∑ b, f (e b)) = 0
  exact (Equiv.sum_comp e f).trans (typeA_row_cyclic (e a))

private def centerCharacterTypeAMap : C →ₗ[ℤ] ZMod (n + 1) :=
  d.centerCharacterLift hsc (fun a => (((e a).val : ℤ) + 1 : ℤ)) (d.centerCharacterTypeA_relations e hA)

include hsc e hA in
private theorem natCard_centerCharacter_A : Nat.card C = n + 1 := by
  rw [d.natCard_centerCharacter_eq_cartanDet hsc e _ hA, cartan_A_det]
  exact_mod_cast (Int.natAbs_natCast (n + 1))

/-- The geometric full centre of type `A n` has the cyclic character group of
order `n + 1`, with the fundamental weights mapped to the consecutive classes. -/
def centerCharacterEquivA (hn : 1 ≤ n) : C ≃ₗ[ℤ] ZMod (n + 1) := by
  let f := d.centerCharacterTypeAMap hsc e hA
  have hcard := d.natCard_centerCharacter_A hsc e hA
  let : Finite C := Nat.finite_of_card_ne_zero (hcard.trans_ne (Nat.succ_ne_zero n))
  let eC : C ≃ ZMod (n + 1) :=
    (Finite.equivFinOfCardEq hcard).trans
      (Finite.equivFinOfCardEq (Nat.card_zmod (n + 1))).symm
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    let i : Fin n := ⟨0, by omega⟩
    refine ⟨a • d.centerFundamentalCharacter hsc (e.symm i), ?_⟩
    rw [map_smul]
    change a • d.centerCharacterTypeAMap hsc e hA
      (d.centerFundamentalCharacter hsc (e.symm i)) = _
    simp [centerCharacterTypeAMap, i]
  exact LinearEquiv.ofBijective f ⟨hsurj.injective_of_finite eC, hsurj⟩

@[simp]
theorem centerCharacterEquivA_fundamental (hn : 1 ≤ n) (a : d.Vertex) :
    d.centerCharacterEquivA hsc e hA hn (d.centerFundamentalCharacter hsc a) =
      (((e a).val : ℤ) + 1 : ℤ) := by
  change d.centerCharacterTypeAMap hsc e hA (d.centerFundamentalCharacter hsc a) = _
  simp [centerCharacterTypeAMap]

private theorem typeA_cyclic_reverse (i : Fin n) :
    (((Fin.revPerm i).val : ℤ) + 1 : ℤ) =
      (-(((i.val : ℤ) + 1 : ℤ) : ZMod (n + 1))) := by
  have hi : ((Fin.revPerm i).val : ℤ) + 1 + ((i.val : ℤ) + 1) = (n : ℤ) + 1 := by
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := i.isLt
    omega
  have hh := congrArg (fun x : ℤ => (x : ZMod (n + 1))) hi
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, ZMod.natCast_self'] at hh
  exact eq_neg_of_add_eq_zero_left (show
    (((Fin.revPerm i).val : ℤ) + 1 : ℤ) + (((i.val : ℤ) + 1 : ℤ) : ZMod (n + 1)) = 0 by
      exact_mod_cast hh)

include hsc e hA in
/-- Each absolute Galois element acts by a single sign on all the
geometric centre characters in type A. -/
theorem centerCharacter_action_sign_A (hn : 1 ≤ n) (σ : Ω ≃ₐ[k] Ω) :
    (∀ χ : C, characterLattice.galoisRepresentation k Ω d.toralCenter.group σ χ = χ) ∨
    (∀ χ : C, characterLattice.galoisRepresentation k Ω d.toralCenter.group σ χ = -χ) := by
  let f := d.centerCharacterEquivA hsc e hA hn
  rcases d.star_cases_of_A e hA σ with hid | hrev
  · left
    intro χ
    obtain ⟨c, rfl⟩ := d.exists_centerCharacter_sum_fundamental hsc χ
    apply f.injective
    simp only [map_sum, map_smul, centerFundamentalCharacter_galois]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [f]
    rw [centerCharacterEquivA_fundamental, centerCharacterEquivA_fundamental, hid]
  · right
    intro χ
    obtain ⟨c, rfl⟩ := d.exists_centerCharacter_sum_fundamental hsc χ
    apply f.injective
    simp only [map_neg, map_sum, map_smul, centerFundamentalCharacter_galois, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [f]
    rw [centerCharacterEquivA_fundamental, centerCharacterEquivA_fundamental, hrev,
      typeA_cyclic_reverse, smul_neg]

end TitsIndexData

end Langlands.GroupScheme
