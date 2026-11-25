/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Degree-zero Čech cohomology of an abelian sheaf

Source: Stacks Project, Cohomology on Sites, Tag 03AN.
(blueprint: lem-weil-pbc-site-cech-zero-cohomology)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

-- Stacks 03AN: compatible zero cocycles have a unique amalgamation.
private theorem cech_zero_glue
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{w})
    (c : S.cochains I.obj 0) (hc : S.differentialValue I.obj 0 c = 0) :
    ∃! x : I.obj.obj (op U), ∀ t, I.obj.map
      (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
  classical
  let P := I.obj ⋙ forget AddCommGrpCat
  have hs : Presieve.IsSheaf J.toGrothendieck P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ I.obj (forget AddCommGrpCat) I.property)
  have hg := (Presieve.isSheafFor_arrows_iff P hom).mp
    (hs.isSheafFor_of_mem_precoverage hcover)
  let a (i : T) := I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op (c (fun _ ↦ i))
  have transport (t : Fin 1 → T) (i : T) (ht : t = fun _ ↦ i)
      (Z : C) (g : Z ⟶ f i) :
      I.obj.map (g ≫ eqToHom (by simpa only [ht] using (S.W_zero t).symm)).op
        (c t) = I.obj.map g.op (a i) := by
    subst t
    rw [op_comp, I.obj.map_comp]
    rfl
  have ha : Presieve.Arrows.Compatible P hom a := by
    intro i j Z gi gj hij
    let t : Fin 2 → T := Fin.cons i (fun _ ↦ j)
    let g : ∀ k : Fin 2, Z ⟶ f (t k) := Fin.cases gi (fun _ ↦ gj)
    obtain ⟨b, hb, _⟩ := S.universal 1 t Z g (by
      intro k
      fin_cases k
      · rfl
      · exact hij.symm)
    have he := congrArg (fun s ↦ I.obj.map b.op (s t)) hc
    change I.obj.map b.op (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
      I.obj.map (S.indexMap t k.succAbove).op (c (t ∘ k.succAbove))) =
        I.obj.map b.op 0 at he
    simp only [Fin.sum_univ_two,
      Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
      map_add, map_neg, map_zero] at he
    have ht0 : t ∘ (0 : Fin 2).succAbove = (fun _ ↦ j) := by
      funext k
      fin_cases k
      rfl
    have ht1 : t ∘ (1 : Fin 2).succAbove = (fun _ ↦ i) := by
      funext k
      fin_cases k
      rfl
    have hm (k : Fin 2) : b ≫ S.indexMap t k.succAbove =
        g (k.succAbove 0) ≫
          eqToHom (S.W_zero (t ∘ k.succAbove)).symm := by
      have : IsIso (S.pr 0 (t ∘ k.succAbove) 0) := by
        rw [S.pr_zero]
        infer_instance
      apply (cancel_mono (S.pr 0 (t ∘ k.succAbove) 0)).mp
      rw [Category.assoc, S.indexMap_pr, hb, Category.assoc, S.pr_zero]
      simp
    simp only [← ConcreteCategory.comp_apply, ← I.obj.map_comp, ← op_comp, hm] at he
    change I.obj.map (gj ≫ eqToHom (S.W_zero (t ∘ (0 : Fin 2).succAbove)).symm).op
      (c (t ∘ (0 : Fin 2).succAbove)) +
      -I.obj.map (gi ≫ eqToHom (S.W_zero (t ∘ (1 : Fin 2).succAbove)).symm).op
        (c (t ∘ (1 : Fin 2).succAbove)) = 0 at he
    rw [transport _ j ht0 Z gj, transport _ i ht1 Z gi] at he
    exact (add_neg_eq_zero.mp he).symm
  obtain ⟨x, hx, hu⟩ := hg a ha
  have hx' : ∀ t, I.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x = c t := by
    intro t
    obtain ⟨i, rfl⟩ : ∃ i, t = (fun _ : Fin 1 ↦ i) := ⟨t 0, by
      funext k
      fin_cases k
      rfl⟩
    have he := congrArg (fun y ↦ I.obj.map (S.pr 0 (fun _ ↦ i) 0).op y) (hx i)
    dsimp [P, a] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
    simp only [← op_comp, S.pr_zero, eqToHom_trans, eqToHom_refl] at he
    simp only [op_id, I.obj.map_id, ConcreteCategory.id_apply] at he
    simpa only [S.pr_zero] using he
  refine ⟨x, hx', ?_⟩
  intro y hy
  apply hu y
  intro i
  have he := congrArg
    (fun z ↦ I.obj.map (eqToHom (S.W_zero (fun _ : Fin 1 ↦ i)).symm).op z)
    (hy (fun _ ↦ i))
  dsimp [P, a] at he ⊢
  change I.obj.map (eqToHom (S.W_zero (fun _ ↦ i)).symm).op
    (I.obj.map (S.pr 0 (fun _ ↦ i) 0 ≫ hom i).op y) = _ at he
  rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp] at he
  simp only [← op_comp, S.pr_zero, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp] at he
  exact he

/-- Degree-zero Čech cohomology of an abelian sheaf is its sections on the covered object.
Source: Stacks Project, Cohomology on Sites, Tag 03AN.
(blueprint: lem-weil-pbc-site-cech-zero-cohomology)

Proof: the alternating degree-zero differential says precisely that the transported
sections on the covering objects agree on every pairwise fibre product. The universal
property of those products makes this the compatibility condition for arbitrary arrows
with equal composites. The sheaf condition therefore gives a unique global section.
Restriction is additive and identifies global sections bijectively with the kernel of
the degree-zero differential. The incoming differential is zero, so abstract homology
is isomorphic to the cycles, which are this concrete kernel. Compose these isomorphisms
with the inverse of restriction. No injectivity or nonempty-cover hypothesis is used. -/
theorem site_cech_zero_cohomology
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U) (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{w}) :
    Nonempty (((S.cohomologyFunctor 0).obj I.obj) ≅ I.obj.obj (op U)) := by
  classical
  have hres (x : I.obj.obj (op U)) : S.differentialValue I.obj 0
      (fun t ↦ I.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x) = 0 := by
    funext t
    have h (k : Fin 2) : I.obj.map (S.indexMap t k.succAbove).op
        (I.obj.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x) =
        I.obj.map (S.pr 1 t 0 ≫ hom (t 0)).op x := by
      rw [← ConcreteCategory.comp_apply, ← I.obj.map_comp, ← op_comp]
      rw [← Category.assoc, S.indexMap_pr, S.comm]
    change (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
      I.obj.map (S.indexMap t k.succAbove).op
        (I.obj.map (S.pr 0 (t ∘ k.succAbove) 0 ≫ hom (t (k.succAbove 0))).op x)) = 0
    simp only [Fin.sum_univ_two, h,
      Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, add_neg_cancel]
  let A := (S.complex I.obj).sc' 0 0 1
  have hg : A.g = S.differential I.obj 0 := by
    change CochainComplex.of.d (S.cochains I.obj) (S.differential I.obj) 0 1 = _
    exact CochainComplex.of_d _ _ 0
  have hker (c : S.cochains I.obj 0) :
      c ∈ AddMonoidHom.ker A.g.hom ↔ S.differentialValue I.obj 0 c = 0 := by
    rw [AddMonoidHom.mem_ker, hg]
    rfl
  let a : I.obj.obj (op U) →+ AddMonoidHom.ker A.g.hom :=
    { toFun := fun x ↦ ⟨fun t ↦ I.obj.map (S.pr 0 t 0 ≫ hom (t 0)).op x, (hker _).mpr (hres x)⟩
      map_zero' := by apply Subtype.ext; funext t; exact map_zero _
      map_add' := by intro x y; apply Subtype.ext; funext t; exact map_add _ _ _ }
  have hinj : Function.Injective a := by
    intro x y hxy
    have hc := (hker (a x).val).mp (a x).property
    obtain ⟨z, _, hu⟩ := cech_zero_glue f hom hcover S I (a x).val hc
    exact (hu x (fun _ ↦ rfl)).trans (hu y (fun t ↦ by
      exact congrFun (congrArg Subtype.val hxy.symm) t)).symm
  have hsurj : Function.Surjective a := by
    intro c
    have hc := (hker c.val).mp c.property
    obtain ⟨x, hx, _⟩ := cech_zero_glue f hom hcover S I c.val hc
    exact ⟨x, Subtype.ext (funext hx)⟩
  let e := AddEquiv.ofBijective a ⟨hinj, hsurj⟩
  let ei : I.obj.obj (op U) ≅ AddCommGrpCat.of (AddMonoidHom.ker A.g.hom) :=
    { hom := AddCommGrpCat.ofHom e.toAddMonoidHom
      inv := AddCommGrpCat.ofHom e.symm.toAddMonoidHom
      hom_inv_id := by ext x; exact e.symm_apply_apply x
      inv_hom_id := by
        apply AddCommGrpCat.ext
        intro x
        exact e.apply_symm_apply x }
  have hf : A.f = 0 := (S.complex I.obj).shape _ _ (by simp)
  exact ⟨(S.complex I.obj).homologyIsoSc' 0 0 1
    CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) ≪≫
      (A.asIsoHomologyπ hf).symm ≪≫ A.abCyclesIso ≪≫ ei.symm⟩

end CategoryTheory
