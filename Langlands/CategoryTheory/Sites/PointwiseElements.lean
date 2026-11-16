import Langlands.CategoryTheory.Sites.PointwiseCovering
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Cofiltered elements and points of generated sites -/

universe u v w

namespace Langlands.CategoryTheory.PointwiseCovering

open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- Any two prescribed elements have a common pointed refinement. -/
def HasCommonPointedRefinements : Prop :=
  ∀ (X Y : C) (x : F.obj X) (y : F.obj Y),
    ∃ (T : C) (p : T ⟶ X) (q : T ⟶ Y) (t : F.obj T),
      F.map p t = x ∧ F.map q t = y

/-- Parallel arrows agreeing on a prescribed element can be equalized
after a refinement that lifts that element. -/
def HasEqualizingPointedRefinements : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y) (x : F.obj X),
    F.map f x = F.map g x →
      ∃ (T : C) (h : T ⟶ X) (t : F.obj T), h ≫ f = h ≫ g ∧ F.map h t = x

/-- Every generating covering presieve is jointly surjective on `F`. -/
def LiftsPrecoverage (J : Precoverage C) : Prop :=
  ∀ ⦃X : C⦄ (R : Presieve X), R ∈ J X →
    ∀ x : F.obj X, ∃ (Y : C) (f : Y ⟶ X), R f ∧ x ∈ Set.range (F.map f)

variable {F}

theorem isCofiltered_elements_of_refinements
    (hne : Nonempty F.Elements)
    (hpair : HasCommonPointedRefinements F)
    (heq : HasEqualizingPointedRefinements F) :
    IsCofiltered F.Elements where
  nonempty := hne
  cone_objs a b := by
    obtain ⟨T, p, q, t, hp, hq⟩ := hpair a.obj b.obj a.val b.val
    exact ⟨F.elementsMk T t, Functor.Elements.homMk p hp,
      Functor.Elements.homMk q hq, trivial⟩
  cone_maps {a b} f g := by
    obtain ⟨T, h, t, hfg, ht⟩ := heq f.hom g.hom a.val
      (f.map_val.trans g.map_val.symm)
    exact ⟨F.elementsMk T t, Functor.Elements.homMk h ht,
      Functor.Elements.hom_ext hfg⟩

theorem hasPointwiseLiftingSquares_of_isCofilteredElements
    [IsCofilteredOrEmpty F.Elements] : HasPointwiseLiftingSquares F := by
  intro X Y S f g x y hxy
  let a := F.elementsMk X x
  let b := F.elementsMk Y y
  let c := F.elementsMk S (F.map g y)
  let f' : a ⟶ c := Functor.Elements.homMk f hxy
  let g' : b ⟶ c := Functor.Elements.homMk g rfl
  obtain ⟨d, p, q, hpq⟩ := IsCofiltered.cospan f' g'
  exact ⟨d.obj, p.hom, q.hom, congrArg (fun k => k.hom) hpq,
    d.val, p.map_val, q.map_val⟩

theorem isJointlySurjective_of_mem_toGrothendieck_of_lifts
    {J : Precoverage C} (hF : HasPointwiseLiftingSquares F)
    (hJ : LiftsPrecoverage F J) {X : C} {S : Sieve X}
    (hS : S ∈ J.toGrothendieck X) : IsJointlySurjective F S := by
  induction hS with
  | of X R hR =>
      intro x
      obtain ⟨Y, f, hf, hx⟩ := hJ R hR x
      exact ⟨Y, f, Sieve.le_generate R _ _ hf, hx⟩
  | top X => exact isJointlySurjective_top X
  | pullback X S hS Y f ih => exact ih.pullback hF f
  | transitive X S R hS hR ihS ihR => exact ihS.transitive ihR

theorem isJointlySurjective_of_mem_toGrothendieck_of_isCofilteredElements
    [IsCofilteredOrEmpty F.Elements] {J : Precoverage C}
    (hJ : LiftsPrecoverage F J) {X : C} {S : Sieve X}
    (hS : S ∈ J.toGrothendieck X) : IsJointlySurjective F S :=
  isJointlySurjective_of_mem_toGrothendieck_of_lifts
    hasPointwiseLiftingSquares_of_isCofilteredElements hJ hS

end Langlands.CategoryTheory.PointwiseCovering
