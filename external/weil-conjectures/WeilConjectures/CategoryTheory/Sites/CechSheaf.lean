/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.CategoryTheory.Sites.CechInjective

/-!
# Čech complexes of sheaves in degree `0`

Let `V : ι → Over X` be a family of objects over `X` whose structure morphisms generate a
covering sieve of `X`, and let `P` be a sheaf of abelian groups. The augmented Čech complex
`0 ⟶ P(X) ⟶ Č⁰(V, P) ⟶ Č¹(V, P)` is exact: this is the sheaf condition for the covering.

Together with `CategoryTheory.Presheaf.exact_cechComplexFunctor_of_injective`, this shows that
the augmented Čech complex of an injective abelian sheaf is exact.

## Main statements

- `CategoryTheory.Presheaf.mono_cechAugmentation_of_isSheaf`: `P(X) ⟶ Č⁰(V, P)` is injective.
- `CategoryTheory.Presheaf.exact_cechAugmentation_of_isSheaf`: exactness at `Č⁰(V, P)`.
- `CategoryTheory.Sheaf.injective_obj`: an injective abelian sheaf is injective as
  a presheaf (Stacks `03F6`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {X : C}
  [HasFiniteProducts (Over X)] {ι : Type w} (V : ι → Over X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max v w})

/-- Components of Čech cochains attached to equal tuples agree after restriction along morphisms
with matching projections. -/
lemma map_cechCochainπ_eq {n : ℕ} (c : (cechOver V P).X n) {W : Over X}
    {y y' : Fin (n + 1) → ι} (h : y = y') (a : W ⟶ cechNerveObj V y)
    (a' : W ⟶ cechNerveObj V y')
    (ha : ∀ l, a ≫ Pi.π _ l ≫ eqToHom (congrArg V (congrFun h l)) = a' ≫ Pi.π _ l) :
    P.map a.left.op (cechCochainπ V P n y c) = P.map a'.left.op (cechCochainπ V P n y' c) := by
  subst h
  obtain rfl : a = a' := Pi.hom_ext _ _ fun l ↦ by simpa using ha l
  rfl

lemma cechCochainπ_cechAugmentation (s : P.obj (op X)) (y : Fin 1 → ι) :
    cechCochainπ V P 0 y (cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ P) s) =
      P.map (cechNerveObj V y).hom.op s := by
  have h := cechAugmentation_π V Over.mkIdTerminal ((Over.forget X).op ⋙ P) y
  have e : (Over.mkIdTerminal.from (cechNerveObj V y)).left = (cechNerveObj V y).hom := by
    simp
  rw [cechCochainπ, ← ConcreteCategory.comp_apply]
  erw [h]
  change P.map (Over.mkIdTerminal.from (cechNerveObj V y)).left.op s = _
  rw [e]
  rfl

/-- The diagonal `V i ⟶ V i ×_X ⋯` into the one-fold product. -/
noncomputable abbrev cechDiag (i : ι) : V i ⟶ cechNerveObj V (fun _ : Fin 1 ↦ i) :=
  Pi.lift fun _ ↦ 𝟙 (V i)

variable {V P}

section

variable (hP : Presheaf.IsSheaf J P)
  (hV : Sieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom) ∈ J X)

omit [HasFiniteProducts (Over X)] in
include hP hV in
lemma isSheafFor_ofArrows :
    (Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (V i).hom)).IsSheafFor
      (P ⋙ forget AddCommGrpCat) := by
  have h : Presieve.IsSheaf J (P ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf (F := forget AddCommGrpCat) P hP)
  exact h.isSheafFor _ hV

include hP hV in
/-- For a sheaf `P`, the augmentation `P(X) ⟶ Č⁰(V, P)` of the Čech complex of a covering is
injective. -/
theorem mono_cechAugmentation_of_isSheaf :
    Mono (cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ P)) := by
  rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro s hs
  have hi (i : ι) : P.map (V i).hom.op s = 0 := by
    have := cechCochainπ_cechAugmentation V P s (fun _ ↦ i)
    rw [hs, map_zero] at this
    have e : (cechDiag V i).left ≫ (cechNerveObj V (fun _ : Fin 1 ↦ i)).hom = (V i).hom := by
      exact Over.w _
    rw [← e, op_comp, P.map_comp, ConcreteCategory.comp_apply, ← this, map_zero]
  obtain ⟨t, -, ht⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 (isSheafFor_ofArrows hP hV)
    (fun _ ↦ 0) (fun i j Z gi gj _ ↦ by
      change P.map gi.op 0 = P.map gj.op 0
      rw [map_zero, map_zero])
  exact (ht s hi).trans (ht 0 fun i ↦ by change P.map _ 0 = 0; exact map_zero _).symm

include hP hV in
/-- For a sheaf `P`, the augmented Čech complex `P(X) ⟶ Č⁰(V, P) ⟶ Č¹(V, P)` of a covering is
exact. -/
theorem exact_cechAugmentation_of_isSheaf :
    (ShortComplex.mk (cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ P))
      ((cechOver V P).d 0 1)
      (cechAugmentation_d V Over.mkIdTerminal ((Over.forget X).op ⋙ P))).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro c hc
  change (cechOver V P).d 0 1 c = 0 at hc
  -- the candidate local sections
  let x (i : ι) : P.obj (op (V i).left) :=
    P.map (cechDiag V i).left.op (cechCochainπ V P 0 (fun _ ↦ i) c)
  have hx : Presieve.Arrows.Compatible (P ⋙ forget AddCommGrpCat) (fun i ↦ (V i).hom) x := by
    intro i j Z gi gj hij
    let W : Over X := Over.mk (gi ≫ (V i).hom)
    let ai : W ⟶ V i := Over.homMk gi
    let aj : W ⟶ V j := Over.homMk gj hij.symm
    let y2 : Fin 2 → ι := Fin.cons i (fun _ : Fin 1 ↦ j)
    let h2 : W ⟶ cechNerveObj V y2 := cechNerveCons V ai (Pi.lift fun _ ↦ aj)
    have hd : P.map (h2 ≫ cechNerveMap V y2 (Fin.succAbove 0)).left.op
          (cechCochainπ V P 0 (y2 ∘ Fin.succAbove 0) c) =
        P.map (h2 ≫ cechNerveMap V y2 (Fin.succAbove 1)).left.op
          (cechCochainπ V P 0 (y2 ∘ Fin.succAbove 1) c) := by
      have := congrArg (P.map h2.left.op) (cechCochainπ_d V P 0 c y2)
      rw [hc, map_zero, map_zero, Fin.sum_univ_two, map_add, map_zsmul, map_zsmul,
        Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_smul] at this
      simp only [Over.comp_left, op_comp, P.map_comp, ConcreteCategory.comp_apply]
      exact add_neg_eq_zero.1 this.symm
    have e₀ := map_cechCochainπ_eq V P c (y := y2 ∘ Fin.succAbove 0) (y' := fun _ ↦ j)
      (by
        funext l
        obtain rfl := Subsingleton.elim (α := Fin 1) l 0
        change y2 (Fin.succAbove 0 0) = j
        rw [show Fin.succAbove (0 : Fin 2) 0 = Fin.succ 0 by decide]
        rfl)
      (h2 ≫ cechNerveMap V y2 (Fin.succAbove 0)) (Pi.lift fun _ ↦ aj) fun l ↦ by
        obtain rfl := Subsingleton.elim (α := Fin 1) l 0
        rw [Category.assoc]
        erw [cechNerveMap_π_assoc]
        exact cechNerveCons_π_of_eq_succ V ai _ (Fin.succAbove (0 : Fin 2) (0 : Fin 1)) 0
          (by decide) _
    have e₁ := map_cechCochainπ_eq V P c (y := y2 ∘ Fin.succAbove 1) (y' := fun _ ↦ i)
      (by
        funext l
        obtain rfl := Subsingleton.elim (α := Fin 1) l 0
        change y2 (Fin.succAbove 1 0) = i
        rw [show Fin.succAbove (1 : Fin 2) 0 = 0 by decide]
        rfl)
      (h2 ≫ cechNerveMap V y2 (Fin.succAbove 1)) (Pi.lift fun _ ↦ ai) fun l ↦ by
        obtain rfl := Subsingleton.elim (α := Fin 1) l 0
        rw [Category.assoc]
        erw [cechNerveMap_π_assoc]
        exact (cechNerveCons_π_of_eq_zero V ai _ (Fin.succAbove (1 : Fin 2) (0 : Fin 1))
          (by decide) _).trans
          (Pi.lift_comp_π (fun _ : Fin 1 ↦ ai) 0).symm
    have fi : (Pi.lift fun _ ↦ ai : W ⟶ cechNerveObj V (fun _ : Fin 1 ↦ i)) =
        ai ≫ cechDiag V i := Pi.hom_ext _ _ fun _ ↦ by simp
    have fj : (Pi.lift fun _ ↦ aj : W ⟶ cechNerveObj V (fun _ : Fin 1 ↦ j)) =
        aj ≫ cechDiag V j := Pi.hom_ext _ _ fun _ ↦ by simp
    have key (k : ι) (a : W ⟶ V k) : P.map a.left.op (x k) =
        P.map (a ≫ cechDiag V k).left.op (cechCochainπ V P 0 (fun _ ↦ k) c) := by
      simp only [x, Over.comp_left, op_comp, P.map_comp, ConcreteCategory.comp_apply]
    change P.map ai.left.op (x i) = P.map aj.left.op (x j)
    rw [key, key, ← fi, ← fj, ← e₀, ← e₁]
    exact hd.symm
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 (isSheafFor_ofArrows hP hV) x hx
  refine ⟨t, cechCochain_ext V P fun y ↦ ?_⟩
  change cechCochainπ V P 0 y
    (cechAugmentation V Over.mkIdTerminal ((Over.forget X).op ⋙ P) t) = _
  rw [cechCochainπ_cechAugmentation]
  have e : (cechNerveObj V y).hom =
      (Pi.π _ 0 : cechNerveObj V y ⟶ V (y 0)).left ≫ (V (y 0)).hom := by
    exact (Over.w _).symm
  rw [e, op_comp, P.map_comp, ConcreteCategory.comp_apply]
  erw [ht (y 0)]
  change P.map _ (P.map _ _) = _
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, ← Over.comp_left]
  have := map_cechCochainπ_eq V P c (y := fun _ ↦ y 0) (y' := y)
    (by funext l; rw [Subsingleton.elim (α := Fin 1) l 0])
    (Pi.π _ 0 ≫ cechDiag V (y 0)) (𝟙 _) fun l ↦ by
      obtain rfl := Subsingleton.elim (α := Fin 1) l 0
      simp
  rw [this]
  simp

end

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

/-- **Injective sheaves are injective presheaves.** The underlying presheaf of an injective
abelian sheaf is injective, as sheafification is exact (Stacks `03F6`). -/
lemma injective_obj (I : Sheaf J AddCommGrpCat.{v}) [Injective I] : Injective I.obj :=
  (sheafificationAdjunction J AddCommGrpCat.{v}).map_injective I ‹_›

end CategoryTheory.Sheaf
