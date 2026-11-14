import Mathlib.CategoryTheory.Sites.JointlySurjective
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-! # Covering points from pointwise lifting squares -/

universe u v w

namespace Langlands.CategoryTheory.PointwiseCovering

open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- Every compatible pair of points lifts to a commuting square in `C`.
The square is not required to be a categorical pullback. -/
def HasPointwiseLiftingSquares : Prop :=
  ∀ ⦃X Y S : C⦄ (f : X ⟶ S) (g : Y ⟶ S) (x : F.obj X) (y : F.obj Y),
    F.map f x = F.map g y →
      ∃ (T : C) (p : T ⟶ X) (q : T ⟶ Y),
        p ≫ f = q ≫ g ∧ ∃ t : F.obj T, F.map p t = x ∧ F.map q t = y

/-- A sieve is jointly surjective on the points supplied by `F`. -/
def IsJointlySurjective {X : C} (S : Sieve X) : Prop :=
  ∀ x : F.obj X, ∃ (Y : C) (f : Y ⟶ X), S f ∧ x ∈ Set.range (F.map f)

variable {F}

theorem isJointlySurjective_top (X : C) :
    IsJointlySurjective F (⊤ : Sieve X) := by
  intro x
  exact ⟨X, 𝟙 X, trivial, x, by simp⟩

theorem IsJointlySurjective.pullback (hF : HasPointwiseLiftingSquares F)
    {X Y : C} {S : Sieve X} (hS : IsJointlySurjective F S) (f : Y ⟶ X) :
    IsJointlySurjective F (S.pullback f) := by
  intro y
  obtain ⟨Z, g, hg, z, hz⟩ := hS (F.map f y)
  obtain ⟨T, p, q, hcomm, t, hp, hq⟩ := hF g f z y hz
  refine ⟨T, q, ?_, t, hq⟩
  change S (q ≫ f)
  rw [← hcomm]
  exact S.downward_closed hg p

theorem IsJointlySurjective.transitive {X : C} {S R : Sieve X}
    (hS : IsJointlySurjective F S)
    (hR : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → IsJointlySurjective F (R.pullback f)) :
    IsJointlySurjective F R := by
  intro x
  obtain ⟨Y, f, hf, y, hy⟩ := hS x
  obtain ⟨Z, g, hg, z, hz⟩ := hR hf y
  refine ⟨Z, g ≫ f, hg, z, ?_⟩
  simpa only [Functor.map_comp, types_comp_apply, hz] using hy

variable (F)

/-- Under pointwise lifting squares, jointly surjective sieves form a
Grothendieck topology. -/
def jointlySurjectiveTopology (hF : HasPointwiseLiftingSquares F) :
    GrothendieckTopology C where
  sieves _ := {S | IsJointlySurjective F S}
  top_mem' X := isJointlySurjective_top X
  pullback_stable' _ _ _ f hS := hS.pullback hF f
  transitive' _ _ hS _ hR := hS.transitive hR

variable {F}

theorem isJointlySurjective_of_mem_toGrothendieck
    (hF : HasPointwiseLiftingSquares F) {X : C} {S : Sieve X}
    (hS : S ∈ (Types.jointlySurjectivePrecoverage.comap F).toGrothendieck X) :
    IsJointlySurjective F S := by
  induction hS with
  | of X R hR =>
      intro x
      obtain ⟨Y, f, hf, hx⟩ :=
        (Presieve.mem_comap_jointlySurjectivePrecoverage_iff F).mp hR x
      exact ⟨Y, f, Sieve.le_generate R _ _ hf, hx⟩
  | top X => exact isJointlySurjective_top X
  | pullback X S hS Y f ih => exact ih.pullback hF f
  | transitive X S R hS hR ihS ihR => exact ihS.transitive ihR

theorem mem_toGrothendieck_iff (hF : HasPointwiseLiftingSquares F)
    {X : C} {S : Sieve X} :
    S ∈ (Types.jointlySurjectivePrecoverage.comap F).toGrothendieck X ↔
      IsJointlySurjective F S := by
  refine ⟨isJointlySurjective_of_mem_toGrothendieck hF, fun hS => ?_⟩
  have h : S.arrows ∈ Types.jointlySurjectivePrecoverage.comap F X :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff F).mpr hS
  simpa using Precoverage.generate_mem_toGrothendieck h

theorem toGrothendieck_eq_jointlySurjectiveTopology (hF : HasPointwiseLiftingSquares F) :
    (Types.jointlySurjectivePrecoverage.comap F).toGrothendieck =
      jointlySurjectiveTopology F hF := by
  ext X S
  exact mem_toGrothendieck_iff hF

end Langlands.CategoryTheory.PointwiseCovering
