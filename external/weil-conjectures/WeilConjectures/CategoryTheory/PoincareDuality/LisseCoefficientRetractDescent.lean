/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.LinearAlgebra.Span.Basic

/-! Descent of natural transformations from scalar generators and retracts. -/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory

/-- Natural transformations descend from scalar generators to their retracts.
Source: the retract and scalar-naturality argument of Weil II (1.1.1) d).
(blueprint: lem-pod-lisse-coefficient-retract-descent).
Proof: naturality on image morphisms extends to their scalar span by linearity.
Choose each object as a retract of an image object and sandwich the given component
between the inclusion and projection. Naturality for the sandwich of any morphism
proves naturality of the extension. Naturality for the inclusion of an image object
proves its restriction is the original transformation. Retracts prove uniqueness. -/
theorem bijective_whiskerLeft_of_span_retract
    {C D : Type*} [Category C] [Category D]
    {K : Type*} [Field K] (T : C ⥤ D) (F : D ⥤ ModuleCat K)
    (hret : ∀ X : D, ∃ A : C, Nonempty (Retract X (T.obj A)))
    (hspan : ∀ (A B : C) (f : T.obj A ⟶ T.obj B),
      F.map f ∈ Submodule.span K (Set.range (fun g : A ⟶ B ↦ F.map (T.map g)))) :
    Function.Bijective (fun u : F ⟶ F ↦ Functor.whiskerLeft T u) := by
  classical
  choose A hr using hret
  let r (X : D) : Retract X (T.obj (A X)) := Classical.choice (hr X)
  have extn {u v : F ⟶ F} (h : Functor.whiskerLeft T u = Functor.whiskerLeft T v) :
      u = v := by
    apply NatTrans.ext
    funext X
    have he := congrArg (fun w ↦ w.app (A X)) h
    change u.app (T.obj (A X)) = v.app (T.obj (A X)) at he
    have hu := u.naturality (r X).i
    have hv := v.naturality (r X).i
    have hi : F.map (r X).i ≫ F.map (r X).r = 𝟙 _ := by
      rw [← F.map_comp, (r X).retract, F.map_id]
    calc
      u.app X = u.app X ≫ (F.map (r X).i ≫ F.map (r X).r) := by rw [hi]; simp
      _ = F.map (r X).i ≫ u.app (T.obj (A X)) ≫ F.map (r X).r := by
        exact (congrArg (fun z ↦ z ≫ F.map (r X).r) hu).symm.trans
          (Category.assoc _ _ _)
      _ = F.map (r X).i ≫ v.app (T.obj (A X)) ≫ F.map (r X).r := by rw [he]
      _ = v.app X := by
        rw [← Category.assoc, hv, Category.assoc, hi, Category.comp_id]
  refine ⟨fun _ _ h ↦ extn h, ?_⟩
  intro u
  have nat (A B : C) (f : T.obj A ⟶ T.obj B) :
      F.map f ≫ u.app B = u.app A ≫ F.map f := by
    suffices ∀ z ∈ Submodule.span K
        (Set.range (fun g : A ⟶ B ↦ F.map (T.map g))),
        z ≫ u.app B = u.app A ≫ z by exact this _ (hspan A B f)
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨g, rfl⟩ := hz
        exact u.naturality g
    | zero => simp
    | add x y hx hy ex ey => simp only [Preadditive.add_comp, Preadditive.comp_add, ex, ey]
    | smul a x hx ex => rw [Linear.smul_comp, Linear.comp_smul, ex]
  let v : F ⟶ F :=
    { app X := F.map (r X).i ≫ u.app (A X) ≫ F.map (r X).r
      naturality := by
        intro X Y f
        have hn := nat (A X) (A Y) ((r X).r ≫ f ≫ (r Y).i)
        have hn' := congrArg (fun z ↦ F.map (r X).i ≫ z ≫ F.map (r Y).r) hn
        have hiX : F.map (r X).i ≫ F.map (r X).r = 𝟙 _ := by
          rw [← F.map_comp, (r X).retract, F.map_id]
        have hiY : F.map (r Y).i ≫ F.map (r Y).r = 𝟙 _ := by
          rw [← F.map_comp, (r Y).retract, F.map_id]
        simpa only [Functor.map_comp, Category.assoc, reassoc_of% hiX, hiY,
          Category.id_comp, Category.comp_id] using hn' }
  refine ⟨v, ?_⟩
  apply NatTrans.ext
  funext X
  have hn := nat X (A (T.obj X)) (r (T.obj X)).i
  change F.map (r (T.obj X)).i ≫ u.app (A (T.obj X)) ≫
    F.map (r (T.obj X)).r = u.app X
  calc
    F.map (r (T.obj X)).i ≫ u.app (A (T.obj X)) ≫ F.map (r (T.obj X)).r =
        (F.map (r (T.obj X)).i ≫ u.app (A (T.obj X))) ≫
          F.map (r (T.obj X)).r := by rw [Category.assoc]
    _ = (u.app X ≫ F.map (r (T.obj X)).i) ≫ F.map (r (T.obj X)).r := by rw [hn]
    _ = u.app X ≫ (F.map (r (T.obj X)).i ≫ F.map (r (T.obj X)).r) := by
      rw [Category.assoc]
    _ = u.app X := by
      rw [← F.map_comp, (r (T.obj X)).retract, F.map_id]
      exact Category.comp_id _

end CategoryTheory
