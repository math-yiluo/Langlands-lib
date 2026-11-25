/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns

/-! # Cancellation of two horizontal Čech deletions

Source: Stacks, Tag 08D1, alternating Čech double complex
(blueprint: lem-sc-principal-cech-horizontal-square).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem deletion_sign {r : ℕ} (S : Finset (Fin r))
    (a b : Fin r) (ha : a ∈ S) (hab : a < b) :
    (-1 : ℤ) ^ (S.filter (fun k ↦ k < a)).card *
        (-1 : ℤ) ^ ((S.erase a).filter (fun k ↦ k < b)).card =
      -((-1 : ℤ) ^ (S.filter (fun k ↦ k < b)).card *
        (-1 : ℤ) ^ ((S.erase b).filter (fun k ↦ k < a)).card) := by
  have h₁ : ((S.erase b).filter (fun k ↦ k < a)) = S.filter (fun k ↦ k < a) := by
    rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
    simp only [Finset.mem_filter, not_and]
    exact fun _ ↦ not_lt_of_ge (le_of_lt hab)
  have h₂ : ((S.erase a).filter (fun k ↦ k < b)).card + 1 =
      (S.filter (fun k ↦ k < b)).card := by
    rw [Finset.filter_erase]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨ha, hab⟩)
  rw [h₁, ← h₂, pow_succ]
  ring

private theorem alternating_erase_sum {r : ℕ} {M : Type*} [AddCommGroup M]
    (S : Finset (Fin r)) (t : Fin r → Fin r → M)
    (ht : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → t a b = t b a) :
    (∑ a ∈ S, ∑ b ∈ S.erase a,
      ((-1 : ℤ) ^ (S.filter (fun k ↦ k < a)).card *
        (-1 : ℤ) ^ ((S.erase a).filter (fun k ↦ k < b)).card) • t a b) = 0 := by
  classical
  let w (ab : Fin r × Fin r) : M :=
    ((-1 : ℤ) ^ (S.filter (fun k ↦ k < ab.1)).card *
      (-1 : ℤ) ^ ((S.erase ab.1).filter (fun k ↦ k < ab.2)).card) • t ab.1 ab.2
  have hw : ∑ ab ∈ S.offDiag, w ab = 0 := by
    have hm (ab : Fin r × Fin r) (hab : ab ∈ S.offDiag) : ab.swap ∈ S.offDiag := by
      exact Finset.mem_offDiag.mpr
        ⟨(Finset.mem_offDiag.mp hab).2.1, (Finset.mem_offDiag.mp hab).1,
          (Finset.mem_offDiag.mp hab).2.2.symm⟩
    refine Finset.sum_involution (fun ab _ ↦ ab.swap) ?_ ?_ hm ?_
    · intro ab hab
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
      have he : t ab.1 ab.2 = t ab.2 ab.1 := ht _ ha _ hb hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · dsimp [w]
        rw [deletion_sign S _ _ ha hlt, he, neg_smul]
        exact neg_add_cancel _
      · dsimp [w]
        rw [deletion_sign S _ _ hb hlt, ← he, neg_smul]
        exact add_neg_cancel _
    · intro ab hab _ heq
      exact (Finset.mem_offDiag.mp hab).2.2 (congrArg Prod.fst heq).symm
    · intro ab _
      exact Prod.swap_swap ab
  rw [Finset.sum_finset_product S.offDiag S (fun a ↦ S.erase a)
    (fun ab ↦ by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)] at hw
  exact hw

private noncomputable def sectionRestriction {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
    (S T : Finset (Fin r))
    (h : principalCechIntersection r f S ≤ principalCechIntersection r f T) :
    principalCechSectionFunctor r f T ⟶ principalCechSectionFunctor r f S :=
  NatTrans.mapHomologicalComplex
    (show affineOpenSections A (principalCechIntersection r f T) ⟶
        affineOpenSections A (principalCechIntersection r f S) from
      { app F := (modulesSpecToSheaf.obj F).obj.map (homOfLE h).op
        naturality := by
          intro F G i
          exact ((modulesSpecToSheaf.map i).hom.naturality _).symm })
    (ComplexShape.up ℤ)

private theorem sectionRestriction_comp {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A) (S T U : Finset (Fin r))
    (h : principalCechIntersection r f S ≤ principalCechIntersection r f T)
    (k : principalCechIntersection r f T ≤ principalCechIntersection r f U)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    (sectionRestriction r f T U k).app F ≫ (sectionRestriction r f S T h).app F =
      (sectionRestriction r f S U (h.trans k)).app F := by
  apply HomologicalComplex.hom_ext
  intro n
  change (modulesSpecToSheaf.obj (F.X n)).obj.map _ ≫
    (modulesSpecToSheaf.obj (F.X n)).obj.map _ =
      (modulesSpecToSheaf.obj (F.X n)).obj.map _
  rw [← Functor.map_comp]
  rfl

private theorem double_erase_card {r : ℕ} (p : ℤ)
    (S : principalCechRowIndex r ((p + 1) + 1)) (a b : Fin r)
    (ha : a ∈ S.val.val) (hb : b ∈ S.val.val.erase a) :
    (((S.val.val.erase a).erase b).card : ℤ) = p + 1 := by
  have h₁ := Finset.card_erase_add_one ha
  have h₂ := Finset.card_erase_add_one hb
  have h₃ := S.property
  omega

private noncomputable def rowRestrictionTerm {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ)
    (S : Finset (Fin r)) (T : Finset (Fin r)) :
    (principalCechColumnFunctor r f p).obj F ⟶
      (principalCechSectionFunctor r f S).obj F := by
  classical
  exact if hc : (T.card : ℤ) = p + 1 then
    if hl : principalCechIntersection r f S ≤ principalCechIntersection r f T then
      if hn : T.Nonempty then
        Limits.Pi.π (fun T : principalCechRowIndex r p ↦
          (principalCechSectionFunctor r f T.val.val).obj F) ⟨⟨T, hn⟩, hc⟩ ≫
          (sectionRestriction r f S T hl).app F
      else 0
    else 0
  else 0

private noncomputable def doubleRestrictionTerm {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ)
    (S : principalCechRowIndex r ((p + 1) + 1)) (a b : Fin r) :
    (principalCechColumnFunctor r f p).obj F ⟶
      (principalCechSectionFunctor r f S.val.val).obj F :=
  rowRestrictionTerm r f F p S.val.val ((S.val.val.erase a).erase b)

private theorem doubleRestrictionTerm_swap {A : Type u} [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ)
    (S : principalCechRowIndex r ((p + 1) + 1)) (a b : Fin r) :
    doubleRestrictionTerm r f F p S a b = doubleRestrictionTerm r f F p S b a := by
  unfold doubleRestrictionTerm
  rw [Finset.erase_right_comm]

/-- Two successive alternating restriction maps compose to zero.
Source: Stacks, Tag 08D1, proof, alternating Čech double complex
(blueprint: lem-sc-principal-cech-horizontal-square).

Proof: project to a target subset S of cardinality p+3. Expand both finite sums
and use the product projection equations. A surviving term deletes two distinct
members a and b of S. Pair the deletion order (a,b) with (b,a). Both terms are the
restriction from S minus {a,b} to S, by functoriality of the section presheaf.
If a<b, deleting a lowers the position of b by one, whereas deleting b leaves
the position of a unchanged. Thus the two integer exponents differ by one and
have opposite signs. Terms with an empty twice-erased subset are absent in both
orders. Every surviving ordered pair has a distinct partner, so the sum is zero.
This calculation holds in every coefficient degree. Product projections and
degree evaluations jointly detect equality of chain maps, proving the result.
Negative p and the empty cover have empty target or source rows and give zero
maps automatically. -/
theorem principalCechHorizontal_square
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
    (principalCechHorizontal r f p).app F ≫
      (principalCechHorizontal r f (p + 1)).app F = 0 := by
  classical
  apply Limits.Pi.hom_ext
  intro S
  simp only [principalCechHorizontal, Category.assoc, Limits.Pi.lift_comp_π,
    Preadditive.comp_sum]
  simp only [Limits.zero_comp]
  have hh : (∑ a ∈ S.val.val, ∑ b ∈ S.val.val.erase a,
      ((-1 : ℤ) ^ (S.val.val.filter (fun k ↦ k < a)).card *
        (-1 : ℤ) ^ ((S.val.val.erase a).filter (fun k ↦ k < b)).card) •
          doubleRestrictionTerm r f F p S a b) = 0 :=
    alternating_erase_sum S.val.val (doubleRestrictionTerm r f F p S)
      (fun a _ b _ _ ↦ doubleRestrictionTerm_swap r f F p S a b)
  rw [← hh]
  rw [← Finset.sum_coe_sort S.val.val]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with hn
  · simp only [Preadditive.comp_zsmul, Limits.Pi.lift_comp_π_assoc,
      Preadditive.sum_comp, Finset.smul_sum]
    rw [← Finset.sum_coe_sort (S.val.val.erase a.val)]
    apply Finset.sum_congr rfl
    intro b _
    have hc := double_erase_card p S a.val b.val a.property b.property
    have hl := (principalCechIntersection_erase_le r f S.val.val a.val).trans
      (principalCechIntersection_erase_le r f (S.val.val.erase a.val) b.val)
    simp only [doubleRestrictionTerm, rowRestrictionTerm, dite_eq_left hc, dite_eq_left hl]
    split_ifs with hn₂
    · simp only [Preadditive.zsmul_comp, smul_smul, Category.assoc]
      congr 2
      exact sectionRestriction_comp r f S.val.val (S.val.val.erase a.val)
        ((S.val.val.erase a.val).erase b.val)
        (principalCechIntersection_erase_le r f S.val.val a.val)
        (principalCechIntersection_erase_le r f (S.val.val.erase a.val) b.val) F
    · simp
  · have he : S.val.val.erase a.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

end AlgebraicGeometry
