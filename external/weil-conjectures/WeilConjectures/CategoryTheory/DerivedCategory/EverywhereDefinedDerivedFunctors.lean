/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

@[expose] public section

universe wA wB vA vB uA uB
open CategoryTheory CategoryTheory.Limits

private noncomputable def denominatorToCostructuredArrow
    {C : Type uA} [Category.{vA} C] {L : Type uB} [Category.{vB} L]
    (W : MorphismProperty C) (Q : C ⥤ L) [Q.IsLocalization W] (X : C) :
    W.Under ⊤ X ⥤ CostructuredArrow Q (Q.obj X) where
  obj s := CostructuredArrow.mk (Localization.isoOfHom Q W s.hom s.prop).inv
  map {s t} f := CostructuredArrow.homMk f.right (by
    apply (cancel_epi (Localization.isoOfHom Q W s.hom s.prop).hom).mp
    simp only [Localization.isoOfHom_hom, CostructuredArrow.mk_hom_eq_self]
    rw [← Category.assoc, ← Q.map_comp, MorphismProperty.Under.w f]
    simp only [Localization.isoOfHom_hom_inv_id])
  map_id s := by ext; rfl
  map_comp f g := by ext; rfl

private theorem leftFraction_leg_eq
    {C : Type uA} [Category.{vA} C] {L : Type uB} [Category.{vB} L]
    {H : Type wA} [Category.{wB} H]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ L) [Q.IsLocalization W] (F : C ⥤ H) (X : C) (Y : H)
    (p : MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F ⟶
      (Functor.const (W.Under ⊤ X)).obj Y)
    {N : C} (a b : W.LeftFraction N X)
    (h : a.map Q (Localization.inverts Q W) = b.map Q (Localization.inverts Q W)) :
    F.map a.f ≫ p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) =
      F.map b.f ≫ p.app (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) := by
  obtain ⟨Z, t₁, t₂, hs, hf, ht⟩ :=
    (MorphismProperty.LeftFraction.map_eq_iff Q W a b).mp h
  let k : W.Under ⊤ X := ⟨Under.mk (a.s ≫ t₁), ht⟩
  let f₁ : (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) ⟶ k :=
    ⟨Under.homMk t₁, trivial, trivial⟩
  let f₂ : (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) ⟶ k :=
    ⟨Under.homMk t₂ hs.symm, trivial, trivial⟩
  have h₁ := p.naturality f₁
  have h₂ := p.naturality f₂
  dsimp at h₁ h₂
  simp only [Category.comp_id] at h₁ h₂
  change F.map t₁ ≫ p.app k = p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) at h₁
  change F.map t₂ ≫ p.app k = p.app (⟨Under.mk b.s, b.hs⟩ : W.Under ⊤ X) at h₂
  rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, ← F.map_comp, ← F.map_comp, hf]

-- Dual of the existing pro-diagram bridge. A fraction gives each cocone leg;
-- common refinement proves independence, and the split witness proves universality.
private theorem rightDerived_defined_pointwiseKan
    {C : Type uA} [Category.{vA} C] {L : Type uB} [Category.{vB} L]
    {H : Type wA} [Category.{wB} H]
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (Q : C ⥤ L) [Q.IsLocalization W] (F : C ⥤ H) (X : C) (Y : H)
    (h : IsEssentiallyConstantIndDiagram
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) Y) :
    Q.HasPointwiseLeftKanExtensionAt F (Q.obj X) := by
  classical
  obtain ⟨_, p, j₀, s, hs, hfactor⟩ := h
  let G := MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F
  let z := fun j : CostructuredArrow Q (Q.obj X) ↦
    (Localization.exists_leftFraction Q W j.hom).choose
  have hz (j : CostructuredArrow Q (Q.obj X)) :
      (z j).map Q (Localization.inverts Q W) = j.hom :=
    (Localization.exists_leftFraction Q W j.hom).choose_spec.symm
  let leg := fun j : CostructuredArrow Q (Q.obj X) ↦
    F.map (z j).f ≫ p.app (⟨Under.mk (z j).s, (z j).hs⟩ : W.Under ⊤ X)
  have hleg (j : CostructuredArrow Q (Q.obj X)) (a : W.LeftFraction j.left X)
      (ha : a.map Q (Localization.inverts Q W) = j.hom) :
      leg j = F.map a.f ≫ p.app (⟨Under.mk a.s, a.hs⟩ : W.Under ⊤ X) :=
    leftFraction_leg_eq W Q F X Y p (z j) a ((hz j).trans ha.symm)
  let ι : CostructuredArrow.proj Q (Q.obj X) ⋙ F ⟶
      (Functor.const (CostructuredArrow Q (Q.obj X))).obj Y :=
    { app := leg
      naturality := by
        intro i j f
        dsimp only [Functor.const_obj_map, Category.comp_id]
        let a : W.LeftFraction i.left X := .mk (f.left ≫ (z j).f) (z j).s (z j).hs
        have ha : a.map Q (Localization.inverts Q W) = i.hom := by
          change Q.map (f.left ≫ (z j).f) ≫ inv (Q.map (z j).s) = i.hom
          rw [Q.map_comp, Category.assoc]
          change Q.map f.left ≫ (z j).map Q (Localization.inverts Q W) = i.hom
          rw [hz j, CostructuredArrow.w f]
        rw [hleg i a ha]
        dsimp [leg, a]
        simp only [Functor.map_comp, Category.assoc, Category.comp_id] }
  have hden (t : W.Under ⊤ X) :
      ι.app (CostructuredArrow.mk (Localization.isoOfHom Q W t.hom t.prop).inv) =
        p.app t := by
    cases t with
    | mk t ht =>
      cases t with
      | mk l r h =>
        cases l
        change leg (CostructuredArrow.mk
          (Localization.isoOfHom Q W h ht).inv) = _
        rw [hleg (CostructuredArrow.mk (Y := r)
          (Localization.isoOfHom Q W h ht).inv)
          (MorphismProperty.LeftFraction.ofInv h ht) (by
          simp [MorphismProperty.LeftFraction.map, MorphismProperty.LeftFraction.ofInv,
            Localization.isoOfHom])]
        change F.map (𝟙 r) ≫ p.app (⟨Under.mk h, ht⟩ : W.Under ⊤ X) = _
        erw [F.map_id, Category.id_comp]
        congr 1
  let c : Cocone G := Cocone.mk Y p
  have hc : IsColimit c :=
    { desc := fun v ↦ s ≫ v.ι.app j₀
      fac := by
        intro v j
        obtain ⟨k, a, b, hab⟩ := hfactor j
        calc
          p.app j ≫ (s ≫ v.ι.app j₀) =
              (p.app j ≫ s ≫ G.map a) ≫ v.ι.app k := by
                simp only [Category.assoc, v.w a]
          _ = G.map b ≫ v.ι.app k := by rw [← hab]
          _ = v.ι.app j := v.w b
      uniq := by
        intro v m hm
        calc
          m = (s ≫ p.app j₀) ≫ m := by rw [hs, Category.id_comp]
          _ = s ≫ v.ι.app j₀ := by rw [Category.assoc, hm j₀] }
  let d : Cocone (CostructuredArrow.proj Q (Q.obj X) ⋙ F) := Cocone.mk Y ι
  let I := denominatorToCostructuredArrow W Q X
  have hd : IsColimit d :=
    { desc := fun v ↦ hc.desc (v.whisker I)
      fac := by
        intro v j
        let a := z j
        let t : W.Under ⊤ X := ⟨Under.mk a.s, a.hs⟩
        let f : j ⟶ I.obj t := CostructuredArrow.homMk a.f (hz j)
        change leg j ≫ hc.desc (v.whisker I) = v.ι.app j
        rw [hleg j a (hz j), Category.assoc]
        change F.map a.f ≫ (c.ι.app t ≫ hc.desc (v.whisker I)) = v.ι.app j
        rw [hc.fac (v.whisker I) t]
        exact v.w f
      uniq := by
        intro v m hm
        apply hc.uniq (v.whisker I) m
        intro t
        change p.app t ≫ m = v.ι.app (I.obj t)
        rw [← hden t]
        exact hm (I.obj t) }
  exact ⟨⟨d, hd⟩⟩

/-- Pointwise essentially constant systems assemble into derived functors.
Source: Stacks Project, Derived Categories, Definition 05S9 and Lemma 05SA.
(auxiliary; not a blueprint node)

The construction chooses the representing values supplied by the hypotheses and
uses the universal comparison maps to define the functors on the localized
categories; functoriality is the content of Lemma 05SA. -/
theorem exists_everywhere_defined_derived_functors
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    (hR : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram D X)
    (hL : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      let D := MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory A, IsEssentiallyConstantProDiagram D X) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (LG : DerivedCategory B ⥤ DerivedCategory A)
      (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF)
      (α : DerivedCategory.Qh ⋙ LG ⟶
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) := by
  classical
  let WA := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let WB := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
  let QA := DerivedCategory.Qh (C := A)
  let QB := DerivedCategory.Qh (C := B)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QB
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QA
  let : Fh.HasPointwiseRightDerivedFunctor WA := fun K ↦ by
    obtain ⟨X, hX⟩ := hR K
    exact (Fh.hasPointwiseRightDerivedFunctorAt_iff QA WA K).2
      (rightDerived_defined_pointwiseKan WA QA Fh K X hX)
  let : Gh.HasPointwiseLeftDerivedFunctor WB := fun M ↦ by
    obtain ⟨X, hX⟩ := hL M
    obtain ⟨u, t₀, r, hr, hfac⟩ := hX.2
    have hb := leftDerived_defined_pointwiseKan_bridge WB QB Gh M X hX u
      ⟨t₀, r, hr, hfac⟩
    exact (Gh.hasPointwiseLeftDerivedFunctorAt_iff QB WB M).2 hb.1
  exact ⟨Fh.totalRightDerived QA WA, Gh.totalLeftDerived QB WB,
    Fh.totalRightDerivedUnit QA WA, Gh.totalLeftDerivedCounit QB WB,
    inferInstance, inferInstance⟩

end
