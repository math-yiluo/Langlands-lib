/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CechCapPresheafLocalIso

/-! # Positive-degree signed insertion before sheafification

Source: Stacks Project, Tags 02FU and 01FM.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

namespace CechInsertion
noncomputable section

open Limits Opposite in
private noncomputable def capIntoCap {X : Scheme.{u}} (G : X.Modules)
    (W Z Y : X.Opens) (h : W ⊓ Z ≤ Y) :
    cechCapModule G Y ⟶ (cechCapPresheafFunctor W).obj (cechCapModule G Z) where
  app V := ModuleCat.ofHom
    (X := (cechCapModule G Y).obj V)
    (Y := ((cechCapPresheafFunctor W).obj (cechCapModule G Z)).obj V)
    { toFun := fun s ↦ G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
      map_add' := by intros; simp
      map_smul' := by
        intro a s
        change G.val.map
            (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
              rw [inf_assoc]; exact inf_le_inf_left _ h)).op
            ((X.ringCatSheaf.obj.map
              (homOfLE (inf_le_left : V.unop ⊓ Y ≤ V.unop)).op a) •
                (show G.val.obj (op (V.unop ⊓ Y)) from s)) =
          (X.ringCatSheaf.obj.map
            (homOfLE (inf_le_left : (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ W)).op
              (X.ringCatSheaf.obj.map
                (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a)) •
            G.val.map
              (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
                rw [inf_assoc]; exact inf_le_inf_left _ h)).op s
        rw [PresheafOfModules.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← RingCat.comp_apply, ← Functor.map_comp,
          ← Functor.map_comp]
        rfl }
  naturality := by
    intro V T f
    ext s
    change G.val.map
        (homOfLE (show (T.unop ⊓ W) ⊓ Z ≤ T.unop ⊓ Y by
          rw [inf_assoc]; exact inf_le_inf_left _ h)).op
        (G.val.map (homOfLE (inf_le_inf_right Y (leOfHom f.unop))).op s) =
      G.val.map
        (homOfLE (inf_le_inf_right Z (inf_le_inf_right W (leOfHom f.unop)))).op
          (G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
            rw [inf_assoc]; exact inf_le_inf_left _ h)).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl

open Limits Opposite in
private theorem capIntoCap_comp {X : Scheme.{u}} (G : X.Modules)
    (W Z Y A : X.Opens) (h : W ⊓ Z ≤ Y) (h' : Y ≤ A) :
    cechCapModuleMap G h' ≫ capIntoCap G W Z Y h =
      capIntoCap G W Z A (h.trans h') := by
  ext V s
  change G.val.map
      (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op
      (G.val.map (homOfLE (inf_le_inf_left V.unop h')).op s) =
    G.val.map
      (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ A by
        rw [inf_assoc]; exact inf_le_inf_left _ (h.trans h'))).op s
  rw [← PresheafOfModules.map_comp_apply]
  rfl

open Limits Opposite in
private theorem capIntoCap_unit {X : Scheme.{u}} (G : X.Modules) (W Z : X.Opens) :
    capIntoCap G W Z Z inf_le_right =
      (cechCapPresheafUnit W).app (cechCapModule G Z) := by
  ext V s
  rfl

/- Insert an absent index into the finite ordered range of a tuple.
Source: Stacks 01FM, ordered indices; 02FU, insertion. -/
open Limits Opposite in
private def insertTuple {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) : Fin (n + 1) ↪o Fin r :=
  (insert i (Finset.univ.map a.toEmbedding)).orderEmbOfFin (by
    rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_fin]
    simpa only [Finset.mem_map, Finset.mem_univ, true_and,
      RelEmbedding.coe_toEmbedding, Set.mem_range]
      using hi)

/- The sign exponent is the number of tuple entries strictly before the inserted index.
Source: Stacks 01FM, ordered signs; 02FU, insertion. -/
open Limits Opposite in
private def position {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r) : ℕ :=
  (Finset.univ.filter fun j ↦ a j < i).card

open Limits Opposite in
private theorem intersection_insert_le {X : Scheme.{u}} {r n : ℕ}
    (U : Fin r → X.Opens) (a : Fin (n + 1) ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) :
    U i ⊓ alternatingCechIntersection U a ≤
      alternatingCechIntersection U (insertTuple a i hi) := by
  apply le_iInf
  intro j
  have hj := Finset.orderEmbOfFin_mem
    (insert i (Finset.univ.map a.toEmbedding))
    (show (insert i (Finset.univ.map a.toEmbedding)).card = (n + 1) + 1 from by
      rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_fin]
      simpa only [Finset.mem_map, Finset.mem_univ, true_and,
        RelEmbedding.coe_toEmbedding, Set.mem_range] using hi) j
  change insertTuple a i hi j ∈ insert i (Finset.univ.map a.toEmbedding) at hj
  rcases Finset.mem_insert.mp hj with h | h
  · rw [h]
    exact inf_le_left
  · rcases Finset.mem_map.mp h with ⟨k, _, hk⟩
    rw [← hk]
    exact inf_le_right.trans (iInf_le (fun k ↦ U (a k)) k)

open Limits Opposite in
private theorem face_omits {r n : ℕ} (a : Fin (n + 1) ↪o Fin r) (b : Fin (n + 1)) :
    a b ∉ Set.range ((Fin.succAboveOrderEmb b).trans a) := by
  rintro ⟨k, hk⟩
  exact Fin.succAbove_ne b k (a.injective hk)

open Limits Opposite in
private theorem insert_face {r n : ℕ} (a : Fin (n + 1) ↪o Fin r) (b : Fin (n + 1)) :
    insertTuple ((Fin.succAboveOrderEmb b).trans a) (a b) (face_omits a b) = a := by
  symm
  apply Finset.orderEmbOfFin_unique'
  intro k
  by_cases hk : k = b
  · subst k
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    exact Finset.mem_map.mpr ⟨l, Finset.mem_univ _, by
      change a (b.succAbove l) = a k
      rw [hl]⟩

open Limits Opposite in
private theorem position_face {r n : ℕ} (a : Fin (n + 1) ↪o Fin r) (b : Fin (n + 1)) :
    position ((Fin.succAboveOrderEmb b).trans a) (a b) = b.val := by
  classical
  dsimp only [position]
  have he : (Finset.univ.filter fun k : Fin n ↦
      ((Fin.succAboveOrderEmb b).trans a) k < a b) =
      (Finset.range b.val).attach.map
        ⟨fun k ↦ (⟨k.val, lt_of_lt_of_le (Finset.mem_range.mp k.prop)
            (Nat.le_of_lt_succ b.is_lt)⟩ : Fin n),
          by intro x y h; apply Subtype.ext; exact congrArg Fin.val h⟩ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, RelEmbedding.trans_apply,
      Fin.succAboveOrderEmb_apply, a.lt_iff_lt, Finset.mem_map, Finset.mem_attach]
    rw [Fin.succAbove_lt_iff_castSucc_lt]
    change k.val < b.val ↔ _
    constructor
    · intro h
      exact ⟨⟨k.val, Finset.mem_range.mpr h⟩, Fin.ext rfl⟩
    · rintro ⟨l, hl⟩
      have hv := congrArg Fin.val hl
      exact hv ▸ Finset.mem_range.mp l.prop
  rw [he, Finset.card_map, Finset.card_attach, Finset.card_range]

/- One signed insertion coordinate, zero if the inserted index is already present.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/
open Limits Opposite in
private def coordinate {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) (a : Fin (q + 1) ↪o Fin r) :
    alternatingCechSheafPresheafTerms U G (q + 1) ⟶
      (cechCapPresheafFunctor (U i)).obj
        (cechCapModule G (alternatingCechIntersection U a)) :=
  if hi : i ∈ Set.range a then 0 else
    (-1 : ℤ) ^ position a i •
      (Pi.π _ (insertTuple a i hi) ≫
        capIntoCap G (U i) (alternatingCechIntersection U a)
          (alternatingCechIntersection U (insertTuple a i hi))
          (intersection_insert_le U a i hi))

/- Assemble signed insertion coordinates by the finite product comparison.
Source: Stacks 02FU, increasing-tuple adaptation of 01FM. -/
open Limits Opposite in
private def map {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) :
    alternatingCechSheafPresheafTerms U G (q + 1) ⟶
      (cechCapPresheafFunctor (U i)).obj (alternatingCechSheafPresheafTerms U G q) :=
  let K := cechCapPresheafFunctor (U i)
  let Q := fun a : Fin (q + 1) ↪o Fin r ↦
    cechCapModule G (alternatingCechIntersection U a)
  let : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  Pi.lift (coordinate U G i q) ≫ inv (piComparison K Q)

open Limits Opposite in
private theorem map_π {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (q : ℕ) (a : Fin (q + 1) ↪o Fin r) :
    map U G i q ≫ (cechCapPresheafFunctor (U i)).map (Pi.π _ a) =
      coordinate U G i q a := by
  let K := cechCapPresheafFunctor (U i)
  let : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  dsimp only [map]
  rw [Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]

open Limits Opposite in
private theorem capIntoCap_map_comp {X : Scheme.{u}} (G : X.Modules)
    (W Z Y A : X.Opens) (h : W ⊓ Z ≤ Y) (h' : A ≤ Z) :
    capIntoCap G W Z Y h ≫ (cechCapPresheafFunctor W).map (cechCapModuleMap G h') =
      capIntoCap G W A Y ((inf_le_inf_left W h').trans h) := by
  ext V s
  change G.val.map (homOfLE (inf_le_inf_left (V.unop ⊓ W) h')).op
      (G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ Z ≤ V.unop ⊓ Y by
        rw [inf_assoc]; exact inf_le_inf_left _ h)).op s) =
    G.val.map (homOfLE (show (V.unop ⊓ W) ⊓ A ≤ V.unop ⊓ Y by
      rw [inf_assoc]; exact inf_le_inf_left _ ((inf_le_inf_left W h').trans h))).op s
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/- The coordinate of insertion followed by the differential: its signed face sum.
Source: Stacks 02FU, ordered deletion calculation as in 01FM. -/
open Limits Opposite in
private def boundaryCoordinate {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (p : ℕ) (a : Fin (p + 2) ↪o Fin r) :
    alternatingCechSheafPresheafTerms U G (p + 1) ⟶
      (cechCapPresheafFunctor (U i)).obj
        (cechCapModule G (alternatingCechIntersection U a)) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (coordinate U G i p ((Fin.succAboveOrderEmb j).trans a) ≫
      (cechCapPresheafFunctor (U i)).map
        (cechCapModuleMap G (alternatingCechIntersection_face_le U p a j)))

open Limits Opposite in
private theorem map_d_π {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (i : Fin r) (p : ℕ) (a : Fin (p + 2) ↪o Fin r) :
    map U G i p ≫ (cechCapPresheafFunctor (U i)).map
        (alternatingCechSheafPresheafD U G p) ≫
      (cechCapPresheafFunctor (U i)).map (Pi.π _ a) =
      boundaryCoordinate U G i p a := by
  let K := cechCapPresheafFunctor (U i)
  let : K.Additive := ⟨by intro A B f g; ext V s; rfl⟩
  rw [← K.map_comp]
  simp only [alternatingCechSheafPresheafD, Pi.lift_comp_π, Functor.map_sum,
    Functor.map_zsmul, Functor.map_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Category.assoc, boundaryCoordinate]
  simp only [K, map_π]

open Limits Opposite in
private theorem intersection_face_cap_le {X : Scheme.{u}} {r q : ℕ}
    (U : Fin r → X.Opens) (a : Fin (q + 2) ↪o Fin r) (b : Fin (q + 2)) :
    U (a b) ⊓ alternatingCechIntersection U ((Fin.succAboveOrderEmb b).trans a) ≤
      alternatingCechIntersection U a := by
  apply le_iInf
  intro k
  cases k using Fin.succAboveCases b with
  | x => exact inf_le_left
  | p k => exact inf_le_right.trans (iInf_le _ k)

open Limits Opposite in
private theorem projection_cap_congr {X : Scheme.{u}} {r q : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (W Z : X.Opens)
    (a b : Fin (q + 1) ↪o Fin r)
    (ha : W ⊓ Z ≤ alternatingCechIntersection U a)
    (hb : W ⊓ Z ≤ alternatingCechIntersection U b) (he : a = b) :
    Pi.π (fun t : Fin (q + 1) ↪o Fin r ↦
      cechCapModule G (alternatingCechIntersection U t)) a ≫
        capIntoCap G W Z (alternatingCechIntersection U a) ha =
    Pi.π _ b ≫ capIntoCap G W Z (alternatingCechIntersection U b) hb := by
  subst b
  rfl

open Limits Opposite in
private theorem coordinate_face {X : Scheme.{u}} {r q : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules)
    (a : Fin (q + 2) ↪o Fin r) (b : Fin (q + 2)) :
    coordinate U G (a b) q ((Fin.succAboveOrderEmb b).trans a) =
      (-1 : ℤ) ^ b.val •
        (Pi.π _ a ≫ capIntoCap G (U (a b))
          (alternatingCechIntersection U ((Fin.succAboveOrderEmb b).trans a))
          (alternatingCechIntersection U a) (intersection_face_cap_le U a b)) := by
  rw [coordinate, dite_eq_right (face_omits a b), position_face]
  exact congrArg ((-1 : ℤ) ^ b.val • ·)
    (projection_cap_congr U G _ _ _ a _ _ (insert_face a b))

open Limits Opposite in
private theorem insertTuple_mem {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) (j : Fin (n + 1)) :
    insertTuple a i hi j ∈ insert i (Finset.univ.map a.toEmbedding) :=
  Finset.orderEmbOfFin_mem _ _ _

open Limits Opposite in
private theorem face_insertTuple {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) (b : Fin (n + 1)) (hb : insertTuple a i hi b = i) :
    (Fin.succAboveOrderEmb b).trans (insertTuple a i hi) = a := by
  let S := Finset.univ.map a.toEmbedding
  have hcard : S.card = n := by simp only [S, Finset.card_map, Finset.card_fin]
  apply (Finset.orderEmbOfFin_unique' hcard _).trans
    (Finset.orderEmbOfFin_unique' hcard (fun k ↦
      Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩)).symm
  intro k
  rcases Finset.mem_insert.mp (insertTuple_mem a i hi (b.succAbove k)) with h | h
  · have he : b.succAbove k = b := (insertTuple a i hi).injective (h.trans hb.symm)
    exact (Fin.succAbove_ne b k he).elim
  · exact h

open Limits Opposite in
private theorem exists_insertTuple_index {r n : ℕ} (a : Fin n ↪o Fin r) (i : Fin r)
    (hi : i ∉ Set.range a) : ∃ b, insertTuple a i hi b = i := by
  have he := Finset.range_orderEmbOfFin (insert i (Finset.univ.map a.toEmbedding))
    (show (insert i (Finset.univ.map a.toEmbedding)).card = n + 1 from by
      rw [Finset.card_insert_of_notMem, Finset.card_map, Finset.card_fin]
      simpa only [Finset.mem_map, Finset.mem_univ, true_and,
        RelEmbedding.coe_toEmbedding, Set.mem_range] using hi)
  change i ∈ Set.range (insertTuple a i hi)
  rw [show Set.range (insertTuple a i hi) =
    ((insert i (Finset.univ.map a.toEmbedding) : Finset (Fin r)) : Set (Fin r))
      from he]
  exact Finset.mem_insert_self _ _

open Limits Opposite in
private theorem deletion_commute {r q : ℕ} (a : Fin (q + 3) ↪o Fin r)
    (b : Fin (q + 3)) (j : Fin (q + 2)) :
    (Fin.succAboveOrderEmb (j.predAbove b)).trans
        ((Fin.succAboveOrderEmb (b.succAbove j)).trans a) =
      (Fin.succAboveOrderEmb j).trans ((Fin.succAboveOrderEmb b).trans a) := by
  apply DFunLike.ext
  intro k
  exact congrArg a (Fin.succAbove_succAbove_succAbove_predAbove b j k)

open Limits Opposite in
private theorem deletion_pivot {r q : ℕ} (a : Fin (q + 3) ↪o Fin r)
    (b : Fin (q + 3)) (j : Fin (q + 2)) :
    ((Fin.succAboveOrderEmb (b.succAbove j)).trans a) (j.predAbove b) = a b := by
  exact congrArg a (Fin.succAbove_succAbove_predAbove b j)

open Limits Opposite in
private theorem deletion_sign {n : ℕ} (b : Fin (n + 1)) (j : Fin n) :
    (-1 : ℤ) ^ j.val * (-1 : ℤ) ^ (j.predAbove b).val =
      -((-1 : ℤ) ^ b.val * (-1 : ℤ) ^ (b.succAbove j).val) := by
  by_cases h : j.castSucc < b
  · rw [Fin.succAbove_of_castSucc_lt _ _ h,
      Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc, Fin.val_pred, ← pow_add]
    have he : j.val + (b.val - 1) + 1 = b.val + j.val := by
      have : 0 < b.val := lt_of_le_of_lt (Nat.zero_le _) h
      omega
    have hh := congrArg (fun n ↦ (-1 : ℤ) ^ n) he
    rw [pow_succ] at hh
    simpa only [mul_neg_one, neg_neg] using congrArg Neg.neg hh
  · have h' := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']
    simp only [Fin.val_succ, Fin.coe_castPred, pow_succ, mul_neg, neg_neg, mul_one]
    exact mul_comm _ _

open Limits Opposite in
private theorem coordinate_of_face {X : Scheme.{u}} {r q : ℕ}
    (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (a : Fin (q + 1) ↪o Fin r) (c : Fin (q + 2) ↪o Fin r) (b : Fin (q + 2))
    (hi : c b = i) (ha : (Fin.succAboveOrderEmb b).trans c = a)
    (h : U i ⊓ alternatingCechIntersection U a ≤ alternatingCechIntersection U c) :
    coordinate U G i q a = (-1 : ℤ) ^ b.val •
      (Pi.π _ c ≫ capIntoCap G (U i) (alternatingCechIntersection U a)
        (alternatingCechIntersection U c) h) := by
  subst i
  subst a
  exact coordinate_face U G c b

end
end CechInsertion

/- For a tuple already containing the inserted index, exactly its deletion survives.
Source: Stacks 02FU, insertion computation; increasing tuples as in 01FM.

Proof: Write i=a b. Every face other than b still contains i, so its insertion
coordinate is zero. The b face omits i; inserting it recovers a, in position b.
The two signs multiply to one. Restriction through the deleted face followed by
intersection with U i is just the cap unit on the a-coordinate. The other
insertion term is zero because a itself contains i. -/
open CechInsertion Limits Opposite in
private theorem alternatingCechPresheaf_insertion_containing_coordinate
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) (a : Fin (p + 2) ↪o Fin r) (hi : i ∈ Set.range a) :
    boundaryCoordinate U G i p a +
      alternatingCechSheafPresheafD U G (p + 1) ≫ coordinate U G i (p + 1) a =
        Pi.π _ a ≫ (cechCapPresheafUnit (U i)).app
          (cechCapModule G (alternatingCechIntersection U a)) := by
  classical
  rcases hi with ⟨b, rfl⟩
  have hzero : coordinate U G (a b) (p + 1) a = 0 := by
    exact dite_eq_left ⟨b, rfl⟩
  rw [hzero, Limits.comp_zero, add_zero]
  rw [boundaryCoordinate, Finset.sum_eq_single b]
  · rw [coordinate_face]
    simp only [Preadditive.zsmul_comp, Category.assoc, capIntoCap_map_comp, smul_smul]
    have hs : (-1 : ℤ) ^ b.val * (-1 : ℤ) ^ b.val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    rw [hs, one_smul, capIntoCap_unit]
  · intro j _ hj
    have hmem : a b ∈ Set.range ((Fin.succAboveOrderEmb j).trans a) := by
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hj)
      exact ⟨k, congrArg a hk⟩
    rw [coordinate, dite_eq_left hmem, Limits.zero_comp, smul_zero]
  · simp

/- Paired noncentral faces cancel on a tuple omitting the inserted index.
Source: Stacks 02FU, the displayed dh+hd computation; increasing tuples as in 01FM.

Proof: Enlarge a by inserting i in its unique position b. In d followed by
insertion at a, the face deleting b is the restriction of the a-coordinate,
since its two signs multiply to one. Each other face, indexed by b.succAbove j,
is the sorted insertion into the j-face of a. Its pivot position is j.predAbove b.
The two deletion orders agree by the succAbove identity. If j<b, the two sign
exponents are j+b-1 and j+b; otherwise they are j+b and j+b+1, so the terms are
negatives. The restrictions compose to the same map to G on V intersect U i
intersect the intersection of a. Summing the paired negatives leaves precisely
the cap unit of the a-coordinate. Empty intersections do not alter the argument;
if the tuple type is empty there is no coordinate to check. No covering condition
or sheafification is used. -/
open CechInsertion Limits Opposite in
private theorem alternatingCechPresheaf_insertion_omitting_coordinate
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) (a : Fin (p + 2) ↪o Fin r) (hi : i ∉ Set.range a) :
    boundaryCoordinate U G i p a +
      alternatingCechSheafPresheafD U G (p + 1) ≫ coordinate U G i (p + 1) a =
        Pi.π _ a ≫ (cechCapPresheafUnit (U i)).app
          (cechCapModule G (alternatingCechIntersection U a)) := by
  classical
  let B := insertTuple a i hi
  obtain ⟨b, hb⟩ := exists_insertTuple_index a i hi
  change B b = i at hb
  have ha : (Fin.succAboveOrderEmb b).trans B = a := face_insertTuple a i hi b hb
  have hB : U i ⊓ alternatingCechIntersection U a ≤ alternatingCechIntersection U B :=
    intersection_insert_le U a i hi
  have ht := coordinate_of_face U G i a B b hb ha hB
  let c (j : Fin (p + 2)) := (Fin.succAboveOrderEmb (b.succAbove j)).trans B
  have hcface (j : Fin (p + 2)) :
      (Fin.succAboveOrderEmb (j.predAbove b)).trans (c j) =
        (Fin.succAboveOrderEmb j).trans a := by
    exact (deletion_commute B b j).trans (congrArg ((Fin.succAboveOrderEmb j).trans ·) ha)
  have hcpivot (j : Fin (p + 2)) : c j (j.predAbove b) = i :=
    (deletion_pivot B b j).trans hb
  have hcap (j : Fin (p + 2)) :
      U i ⊓ alternatingCechIntersection U ((Fin.succAboveOrderEmb j).trans a) ≤
        alternatingCechIntersection U (c j) := by
    have h := intersection_face_cap_le U (c j) (j.predAbove b)
    rw [hcpivot, hcface] at h
    exact h
  have hc (j : Fin (p + 2)) := coordinate_of_face U G i
    ((Fin.succAboveOrderEmb j).trans a) (c j) (j.predAbove b)
    (hcpivot j) (hcface j) (hcap j)
  rw [ht]
  simp only [Preadditive.comp_zsmul, ← Category.assoc,
    alternatingCechSheafPresheafD, Pi.lift_comp_π, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  simp only [Category.assoc, capIntoCap_comp]
  rw [Fin.sum_univ_succAbove _ b]
  simp only [Finset.smul_sum, smul_add, smul_smul]
  have hcentral : (-1 : ℤ) ^ b.val * (-1 : ℤ) ^ b.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [hcentral, one_smul]
  have hcenter := projection_cap_congr U G (U i) (alternatingCechIntersection U a)
    ((Fin.succAboveOrderEmb b).trans B) a
    (hB.trans (alternatingCechIntersection_face_le U (p + 1) B b)) inf_le_right ha
  rw [hcenter, capIntoCap_unit]
  have hcancel : boundaryCoordinate U G i p a =
      -(∑ j : Fin (p + 2),
        ((-1 : ℤ) ^ b.val * (-1 : ℤ) ^ (b.succAbove j).val) •
          (Pi.π _ (c j) ≫ capIntoCap G (U i) (alternatingCechIntersection U a)
            (alternatingCechIntersection U (c j))
            (hB.trans (alternatingCechIntersection_face_le U (p + 1) B
              (b.succAbove j))))) := by
    rw [boundaryCoordinate, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hc j]
    simp only [Preadditive.zsmul_comp, Category.assoc, capIntoCap_map_comp, smul_smul]
    rw [deletion_sign, neg_smul]
  rw [hcancel]
  abel

/-- The positive insertion identity valued in intersection presheaves.
Source: Stacks Project, Tag 02FU, local insertion; Tag 01FM, increasing tuples.
(blueprint: lem-pc-s3-alternating-cech-presheaf-positive-insertion).

Proof: Write W=U i and K(P)(V)=P(V intersect W), with scalars restricted
from V. For an increasing tuple a of length q+1, define the a-coordinate
of the degree-q insertion map from P(q+1) to K(Pq) by zero if i occurs
in a. Otherwise insert i in its unique increasing position b, project
to that tuple, restrict to V intersect W intersect the intersection of a,
and multiply by (-1)^b. These opens coincide with the inserted tuple's
intersection with V; their equality provides a linear section map.
The maps commute with restriction. The finite product comparison for K
identifies these coordinate maps with a morphism to K(Pq). Use q=p for s
and q=p+1 for t. To check the equation, project to a tuple a of length p+2
and evaluate on V. If a omits i, in the face sum of the inserted tuple
the face deleting i contributes restriction of the a-coordinate to W.
Each other deletion pairs with inserting i after that deletion, with the
same restriction and opposite sign. More precisely, if the inserted index
has position b and a face deletes position j<b, the two exponents are
j+b-1 and j+b. If j is at least b, they are j+b and j+b+1. The face
omitting the inserted i has the product of two signs (-1)^b, hence sign
one. If a contains i, insertion at a is
zero, and among its faces only deleting i permits insertion; the two
signs are (-1)^b and their product is one. Thus s K(d)+d t is exactly
restriction to W in every coordinate. Product extensionality proves the
presheaf equality. This argument needs no cover condition. Empty opens
and empty tuple index sets are zero modules; if r=0 no index i exists.
There is no sheafification or extension to integer degrees in this claim. -/
theorem alternatingCechSheafPresheaf_positive_insertion
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) :
    let K := cechCapPresheafFunctor (U i)
    let P₀ := alternatingCechSheafPresheafTerms U G p
    let P₁ := alternatingCechSheafPresheafTerms U G (p + 1)
    let P₂ := alternatingCechSheafPresheafTerms U G (p + 1 + 1)
    ∃ (s : P₁ ⟶ K.obj P₀) (t : P₂ ⟶ K.obj P₁),
      (cechCapPresheafUnit (U i)).app P₁ =
        s ≫ K.map (alternatingCechSheafPresheafD U G p) +
          alternatingCechSheafPresheafD U G (p + 1) ≫ t := by
  classical
  dsimp only
  let K := cechCapPresheafFunctor (U i)
  let Q := fun a : Fin (p + 2) ↪o Fin r ↦
    cechCapModule G (alternatingCechIntersection U a)
  let : K.IsRightAdjoint :=
    inferInstanceAs (PresheafOfModules.pushforward (cechCapRingMap (U i))).IsRightAdjoint
  refine ⟨CechInsertion.map U G i p, CechInsertion.map U G i (p + 1), ?_⟩
  apply (cancel_mono (Limits.piComparison K Q)).mp
  apply Limits.Pi.hom_ext
  intro a
  simp only [Category.assoc, Limits.piComparison_comp_π, Preadditive.add_comp]
  rw [CechInsertion.map_d_π, CechInsertion.map_π]
  have hn := (cechCapPresheafUnit (U i)).naturality (Limits.Pi.π Q a)
  change Limits.Pi.π Q a ≫ (cechCapPresheafUnit (U i)).app (Q a) =
    (cechCapPresheafUnit (U i)).app (alternatingCechSheafPresheafTerms U G (p + 1)) ≫
      K.map (Limits.Pi.π Q a) at hn
  rw [← hn]
  by_cases hi : i ∈ Set.range a
  · exact (alternatingCechPresheaf_insertion_containing_coordinate U G i p a hi).symm
  · exact (alternatingCechPresheaf_insertion_omitting_coordinate U G i p a hi).symm

end AlgebraicGeometry
