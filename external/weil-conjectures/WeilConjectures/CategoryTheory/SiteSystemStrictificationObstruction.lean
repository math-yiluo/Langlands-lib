/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# An obstruction to strictifying systems of finite precoverages

Source: the indexed base-change axiom in Mathlib's `Precoverage.IsStableUnderBaseChange`,
applied to the construction of Stacks Project, Categories, Tag 004A.
(blueprint: lem-weil-pbc-site-system-strictification-obstruction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem finite_of_injective_iso_family
    {C A : Type u} [SmallCategory C] [Nonempty A]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderBaseChange]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ J X → Finite R.uncurry)
    (X : C) (Y : A → C) (hY : Function.Injective Y) (s : ∀ a, Y a ≅ X) :
    Finite A := by
  classical
  have hid : Presieve.ofArrows (fun _ : A ↦ X) (fun _ ↦ 𝟙 X) =
      Presieve.singleton (𝟙 X) := by
    funext Z f
    apply propext
    constructor
    · rintro ⟨a⟩
      exact Presieve.singleton_self _
    · rintro ⟨⟩
      exact Presieve.ofArrows.mk (Classical.arbitrary A)
  have hcov : Presieve.ofArrows Y (fun a ↦ (s a).hom) ∈ J X := by
    apply Precoverage.mem_coverings_of_isPullback (fun _ : A ↦ 𝟙 X)
      (by rw [hid]; exact Precoverage.mem_coverings_of_isIso (𝟙 X)) (𝟙 X)
      (fun a ↦ (s a).hom) (fun a ↦ (s a).hom)
    intro a
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  let R := Presieve.ofArrows Y (fun a ↦ (s a).hom)
  have : Finite R.uncurry := hfinite X R hcov
  let f : A → R.uncurry := fun a ↦ ⟨⟨Y a, (s a).hom⟩, Presieve.ofArrows.mk a⟩
  exact Finite.of_injective f (fun a b h ↦ hY (congrArg (fun z ↦ z.val.1) h))

/-- Source: Mathlib `Precoverage.IsStableUnderBaseChange`, together with the strict
coefficient equalities in Stacks Project, Categories, Tag 004A, applied fibrewise.
(blueprint: lem-weil-pbc-site-system-strictification-obstruction).

Proof: put every transition image of the one source object in the category at the
largest index. Its image under the coefficient functor is its original index, by
both strict equalities. Thus these objects form an injective family indexed by I.
Essential surjectivity of the equivalence at the largest index makes every one
of them isomorphic to the image of the unique source object. The singleton identity
covering may be indexed by I, repeating its one arrow. Pull it back along the
identity using these isomorphisms as both legs of the pullback squares. The indexed
base-change axiom makes the resulting family covering. Its uncurry contains an
injective image of I, contradicting the assumed finiteness of every covering.
No preservation or continuity assumptions are needed for this obstruction. -/
theorem site_system_strictification_obstruction
    (I : Type u) [Preorder I] [OrderTop I] [Infinite I]
    (C : Type u) [SmallCategory C] [Subsingleton C] (c : C)
    (F : I ⥤ Cat.{u, u}) (Q : ∀ i : I, Precoverage (F.obj i))
    [∀ i, (Q i).HasIsos] [∀ i, (Q i).IsStableUnderBaseChange]
    (hfinite : ∀ (i : I) (X : F.obj i) (R : Presieve X),
      R ∈ Q i X → Finite R.uncurry)
    (e : ∀ i : I, C ⥤ F.obj i) [∀ i, (e i).IsEquivalence]
    (v' : ∀ i : I, F.obj i ⥤ Codiscrete I)
    (hstrict : ∀ (i j : I) (h : i ≤ j),
      (F.map (homOfLE h)).toFunctor ⋙ v' j = v' i)
    (hretract : ∀ i : I, e i ⋙ v' i = Codiscrete.functor (fun _ : C ↦ i)) :
    False := by
  classical
  let Y : I → F.obj ⊤ := fun i ↦ (F.map (homOfLE (le_top : i ≤ ⊤))).toFunctor.obj
    ((e i).obj c)
  have hlabel (i : I) : ((v' ⊤).obj (Y i)).as = i := by
    calc
      ((v' ⊤).obj (Y i)).as = ((v' i).obj ((e i).obj c)).as :=
        congrArg (fun G : F.obj i ⥤ Codiscrete I ↦ (G.obj ((e i).obj c)).as)
          (hstrict i ⊤ le_top)
      _ = i := congrArg (fun G : C ⥤ Codiscrete I ↦ (G.obj c).as) (hretract i)
  have hY : Function.Injective Y := by
    intro i j h
    rw [← hlabel i, ← hlabel j, h]
  let s (i : I) : Y i ≅ (e ⊤).obj c :=
    ((e ⊤).objObjPreimageIso (Y i)).symm ≪≫
      eqToIso (congrArg (e ⊤).obj (Subsingleton.elim ((e ⊤).objPreimage (Y i)) c))
  have : Finite I := finite_of_injective_iso_family (Q ⊤) (hfinite ⊤)
    ((e ⊤).obj c) Y hY s
  exact not_finite I

end CategoryTheory
