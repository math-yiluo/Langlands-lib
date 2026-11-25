/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.CyclePullbackTower
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Pointwise comparisons for the explicit cycle-pullback tower. -/

@[expose] public section

universe v u vB uB
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.CyclePullback

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B]

/-- The integer-indexed stage, using the actual tower's maps. -/
private noncomputable def indexedStage (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) : Stage F where
  degree := i
  current := term T π F N i
  next := term T π F N (i + 1)
  d := differential T π F N i
  e := augmentation T π F N i

private theorem stage_transport (F : B ⥤ CochainComplex A ℤ) (s : Stage F)
    (i : ℤ) (X Y : B ⥤ A) (hc : X = s.current) (hn : s.next = Y)
    (hg : s.degree = i) :
    (Stage.mk i X Y (eqToHom hc ≫ s.d ≫ eqToHom hn)
      (eqToHom hc ≫ s.e ≫ eqToHom (congrArg (targetTerm F) hg))) = s := by
  cases s
  cases hg
  cases hc
  cases hn
  simp

private theorem stage_d_eq {F : B ⥤ CochainComplex A ℤ} (s t : Stage F) (h : s = t) :
    s.d = eqToHom (congrArg Stage.current h) ≫ t.d ≫
      eqToHom (congrArg Stage.next h).symm := by
  cases h
  simp

private theorem stage_e_eq {F : B ⥤ CochainComplex A ℤ} (s t : Stage F) (h : s = t) :
    s.e = eqToHom (congrArg Stage.current h) ≫ t.e ≫
      eqToHom (congrArg (targetTerm F) (congrArg Stage.degree h).symm) := by
  cases h
  simp

private theorem indexedStage_eq (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    indexedStage T π F N i = tower T π F N (depth N i) := by
  unfold indexedStage differential augmentation
  simp only [dite_eq_left hi]
  exact stage_transport F _ i _ _ (term_eq T π F N i hi)
    (tower_next T π F N i hi) (degree_eq T π F N i hi)

private theorem indexedStage_above (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) :
    indexedStage T π F N (N + 1) = initial F N := by
  have h₁ : ¬ N + 1 ≤ N := by omega
  have h₂ : ¬ N + 1 + 1 ≤ N := by omega
  have hc : term T π F N (N + 1) = (initial F N).current := by
    simp only [term, ite_eq_right h₁, initial]
  have hn : (initial F N).next = term T π F N (N + 1 + 1) := by
    simp only [term, ite_eq_right h₂, initial]
  convert stage_transport F (initial F N) (N + 1) _ _ hc hn rfl using 1
  simp only [indexedStage, differential, augmentation, dite_eq_right h₁, initial,
    comp_zero, zero_comp]

private theorem indexedStage_step (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    indexedStage T π F N i = step T π (indexedStage T π F N (i + 1)) := by
  by_cases h : i = N
  · subst i
    rw [indexedStage_above, indexedStage_eq T π F N N (le_refl _)]
    simp [depth, tower]
  · have hn : i + 1 ≤ N := by omega
    rw [indexedStage_eq T π F N i hi, indexedStage_eq T π F N (i + 1) hn]
    have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
    rw [hd, tower]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluate a pullback over a kernel, using the canonical limit comparisons.
(blueprint: def-tower-canonical-comparison-g3). -/
noncomputable def evaluatedPullbackIso {X Y Y' Z : B ⥤ A}
    (f : X ⟶ Z) (d : Y ⟶ Y') (e : Y ⟶ Z) (b : B) :
    (pullback f (kernel.ι d ≫ e)).obj b ≅
      pullback (f.app b) (kernel.ι (d.app b) ≫ e.app b) :=
  PreservesPullback.iso ((evaluation B A).obj b) f (kernel.ι d ≫ e) ≪≫
    asIso (pullback.map (((evaluation B A).obj b).map f)
      (((evaluation B A).obj b).map (kernel.ι d ≫ e))
      (f.app b) (kernel.ι (d.app b) ≫ e.app b) (𝟙 _) (PreservesKernel.iso
      ((evaluation B A).obj b) d).hom (𝟙 _) (by simp) (by
        simp only [PreservesKernel.iso_hom, Category.comp_id]
        simpa only [Functor.map_comp, Category.assoc, evaluation_obj_map, NatTrans.comp_app] using
          (kernelComparison_comp_ι d ((evaluation B A).obj b)).symm =≫ e.app b))

set_option backward.isDefEq.respectTransparency false in
private theorem evaluatedPullbackIso_fst {X Y Y' Z : B ⥤ A}
    (f : X ⟶ Z) (d : Y ⟶ Y') (e : Y ⟶ Z) (b : B) :
    (evaluatedPullbackIso f d e b).hom ≫ pullback.fst _ _ =
      (pullback.fst f (kernel.ι d ≫ e)).app b := by
  simp only [evaluatedPullbackIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_fst, Category.comp_id]
  exact PreservesPullback.iso_hom_fst ((evaluation B A).obj b) f (kernel.ι d ≫ e)

set_option backward.isDefEq.respectTransparency false in
private theorem evaluatedPullbackIso_snd {X Y Y' Z : B ⥤ A}
    (f : X ⟶ Z) (d : Y ⟶ Y') (e : Y ⟶ Z) (b : B) :
    (evaluatedPullbackIso f d e b).hom ≫ pullback.snd _ _ ≫ kernel.ι (d.app b) =
      (pullback.snd f (kernel.ι d ≫ e) ≫ kernel.ι d).app b := by
  simp only [evaluatedPullbackIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullback.map, pullback.lift_snd_assoc, PreservesKernel.iso_hom]
  have hk := kernelComparison_comp_ι d ((evaluation B A).obj b)
  have hp := PreservesPullback.iso_hom_snd ((evaluation B A).obj b) f (kernel.ι d ≫ e)
  simp only [evaluation_obj_map] at hk hp
  rw [hk, ← Category.assoc]
  simpa only [evaluation_obj_map, NatTrans.comp_app] using hp =≫ (kernel.ι d).app b

/-- The functor-category pullback used at degree `i`.
(blueprint: def-tower-canonical-comparison-g3). -/
noncomputable def indexedPullback (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) : B ⥤ A :=
  pullback (targetD F i (i + 1))
    (kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1))

/-- The term is the explicit next pullback followed by `T`.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: def-tower-canonical-comparison-g3). -/
theorem term_step_eq (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    term T π F N i = indexedPullback T π F N i ⋙ T := by
  have hd : i + 1 - 1 = i := by omega
  have h := congrArg Stage.current (indexedStage_step T π F N i hi)
  dsimp only [indexedStage, step, stepPullback, cyclesArrow] at h
  have hp := congrArg (fun j : ℤ ↦
    pullback (targetD F j (i + 1))
      (kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1))) hd
  exact h.trans (congrArg (fun G : B ⥤ A ↦ G ⋙ T) hp)

private theorem pullback_fst_transport (F : B ⥤ CochainComplex A ℤ)
    {Y Z : B ⥤ A} (f : ∀ j : ℤ, targetTerm F j ⟶ Z) (g : Y ⟶ Z)
    {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (fun j ↦ pullback (f j) g) h) ≫ pullback.fst (f k) g =
      pullback.fst (f j) g ≫ eqToHom (congrArg (targetTerm F) h) := by
  cases h
  simp

private theorem pullback_snd_transport (F : B ⥤ CochainComplex A ℤ)
    {Y Z : B ⥤ A} (f : ∀ j : ℤ, targetTerm F j ⟶ Z) (g : Y ⟶ Z)
    {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (fun j ↦ pullback (f j) g) h) ≫ pullback.snd (f k) g =
      pullback.snd (f j) g := by
  cases h
  simp

omit [Abelian A] in
private theorem whisker_transport (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {G H : B ⥤ A} (h : G = H) :
    eqToHom (congrArg (fun G : B ⥤ A ↦ G ⋙ T) h) ≫ Functor.whiskerLeft H π =
      Functor.whiskerLeft G π ≫ eqToHom h := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem indexed_augmentation (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    eqToHom (term_step_eq T π F N i hi) ≫
      Functor.whiskerLeft (indexedPullback T π F N i) π ≫
      pullback.fst (targetD F i (i + 1))
        (kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1)) =
      augmentation T π F N i := by
  have hd : i + 1 - 1 = i := by omega
  let g := kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1)
  let q := fun j : ℤ ↦ pullback (targetD F j (i + 1)) g
  have hs := indexedStage_step T π F N i hi
  have hc := congrArg Stage.current hs
  have hp := congrArg q hd
  have he := stage_e_eq _ _ hs
  dsimp only [indexedStage, step] at he
  simp only [Category.assoc] at he
  change augmentation T π F N i = eqToHom hc ≫
    Functor.whiskerLeft (q (i + 1 - 1)) π ≫
    pullback.fst (targetD F (i + 1 - 1) (i + 1)) g ≫
    eqToHom (congrArg (targetTerm F) hd) at he
  change eqToHom (hc.trans (congrArg (fun G : B ⥤ A ↦ G ⋙ T) hp)) ≫
    Functor.whiskerLeft (q i) π ≫ pullback.fst (targetD F i (i + 1)) g = _
  rw [← eqToHom_trans hc (congrArg (fun G : B ⥤ A ↦ G ⋙ T) hp),
    Category.assoc, ← Category.assoc _ _ (pullback.fst _ _), whisker_transport T π hp]
  simp only [Category.assoc]
  rw [pullback_fst_transport F
    (fun j ↦ targetD F j (i + 1)) g hd]
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem indexed_differential (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    eqToHom (term_step_eq T π F N i hi) ≫
      Functor.whiskerLeft (indexedPullback T π F N i) π ≫
      pullback.snd (targetD F i (i + 1))
        (kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1)) ≫
      kernel.ι (differential T π F N (i + 1)) = differential T π F N i := by
  have hd : i + 1 - 1 = i := by omega
  let g := kernel.ι (differential T π F N (i + 1)) ≫ augmentation T π F N (i + 1)
  let q := fun j : ℤ ↦ pullback (targetD F j (i + 1)) g
  have hs := indexedStage_step T π F N i hi
  have hc := congrArg Stage.current hs
  have hp := congrArg q hd
  have he := stage_d_eq _ _ hs
  dsimp only [indexedStage, step] at he
  simp only [eqToHom_refl, Category.comp_id] at he
  change differential T π F N i = eqToHom hc ≫
    Functor.whiskerLeft (q (i + 1 - 1)) π ≫
    pullback.snd (targetD F (i + 1 - 1) (i + 1)) g ≫
    kernel.ι (differential T π F N (i + 1)) at he
  change eqToHom (hc.trans (congrArg (fun G : B ⥤ A ↦ G ⋙ T) hp)) ≫
    Functor.whiskerLeft (q i) π ≫ pullback.snd (targetD F i (i + 1)) g ≫
    kernel.ι (differential T π F N (i + 1)) = _
  rw [← eqToHom_trans hc (congrArg (fun G : B ⥤ A ↦ G ⋙ T) hp),
    Category.assoc, ← Category.assoc _ _ (pullback.snd _ _ ≫ _),
    whisker_transport T π hp]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom hp), pullback_snd_transport F
    (fun j ↦ targetD F j (i + 1)) g hd]
  exact he.symm

/-- The canonical comparison is obtained by evaluating the recursive pullback and
kernel and applying `T.mapIso`; its data uses only proved equalities.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: def-tower-canonical-comparison-g3). -/
noncomputable def canonicalComparison (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    (term T π F N i).obj b ≅
      T.obj (pullback ((F.obj b).d i (i + 1))
        (kernel.ι ((differential T π F N (i + 1)).app b) ≫
          (augmentation T π F N (i + 1)).app b)) :=
  eqToIso (congrArg (fun G : B ⥤ A ↦ G.obj b) (term_step_eq T π F N i hi)) ≪≫
    T.mapIso (evaluatedPullbackIso (targetD F i (i + 1))
      (differential T π F N (i + 1)) (augmentation T π F N (i + 1)) b)

set_option backward.isDefEq.respectTransparency false in
/-- First projection equation for the canonical comparison.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: new-tower-comparison-first). -/
theorem tower_comparison_canonical_first (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    (canonicalComparison T π F N b i hi).hom ≫ π.app _ ≫ pullback.fst _ _ =
      (augmentation T π F N i).app b := by
  let c := evaluatedPullbackIso (targetD F i (i + 1))
    (differential T π F N (i + 1)) (augmentation T π F N (i + 1)) b
  dsimp only [canonicalComparison, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [← Category.assoc (T.map c.hom) (π.app _) (pullback.fst _ _), π.naturality]
  simp only [Functor.id_map, Category.assoc]
  erw [evaluatedPullbackIso_fst]
  have h := NatTrans.congr_app (indexed_augmentation T π F N i hi) b
  simpa [indexedPullback, targetTerm] using h

set_option backward.isDefEq.respectTransparency false in
/-- Second projection equation for the explicitly constructed canonical comparison.
Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: new-tower-comparison-second). -/
theorem tower_comparison_second {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    (canonicalComparison T π F N b i hi).hom ≫ π.app _ ≫ pullback.snd _ _ ≫
      kernel.ι ((differential T π F N (i + 1)).app b) =
      (differential T π F N i).app b := by
  let c := evaluatedPullbackIso (targetD F i (i + 1))
    (differential T π F N (i + 1)) (augmentation T π F N (i + 1)) b
  dsimp only [canonicalComparison, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  erw [← Category.assoc (T.map c.hom) (π.app _) (pullback.snd _ _ ≫ _), π.naturality]
  simp only [Functor.id_map, Category.assoc]
  erw [evaluatedPullbackIso_snd]
  have h := NatTrans.congr_app (indexed_differential T π F N i hi) b
  simpa [indexedPullback, targetTerm, Category.assoc] using h

/-- (blueprint: lem-pc-cycle-pullback-tower-comparison-stage3) -/
theorem tower_comparison {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) (b : B) (i : ℤ) (hi : i ≤ N) :
    let d := (differential T π F N (i + 1)).app b
    let f := (F.obj b).d i (i + 1)
    let g := kernel.ι d ≫ (augmentation T π F N (i + 1)).app b
    ∃ (c : (term T π F N i).obj b ≅ T.obj (pullback f g)),
      c.hom ≫ π.app (pullback f g) ≫ pullback.fst f g =
        (augmentation T π F N i).app b ∧
      c.hom ≫ π.app (pullback f g) ≫ pullback.snd f g ≫ kernel.ι d =
        (differential T π F N i).app b := by
  dsimp
  let c := canonicalComparison T π F N b i hi
  refine ⟨c, tower_comparison_canonical_first T π F N b i hi, ?_⟩
  exact tower_comparison_second T π F N b i hi

end CochainComplex.CyclePullback
