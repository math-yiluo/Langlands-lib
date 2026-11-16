import Langlands.Cohomology.SiteCech.SplitContraction
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Homology.Functor

/-! # Čech nerves and functors preserving their wide pullbacks -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u₁ v₁ u₂ v₂

variable {A : Type u₁} [Category.{v₁} A] {D : Type u₂} [Category.{v₂} D]
variable (F : A ⥤ D) (f : Arrow A)

/-- Applying a functor to a Čech wide cospan gives the wide cospan of its image. -/
def cechWideCospanCompIso (n : ℕ) :
    WidePullbackShape.wideCospan f.right (fun _ : Fin (n + 1) => f.left)
      (fun _ => f.hom) ⋙ F ≅
    WidePullbackShape.wideCospan (F.obj f.right) (fun _ : Fin (n + 1) => F.obj f.left)
      (fun _ => F.map f.hom) :=
  WidePullbackShape.functorExt (Iso.refl _) (fun _ => Iso.refl _)
    (by intro j; simp)

variable
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)]
  [∀ n : ℕ, HasWidePullback (F.obj f.right) (fun _ : Fin (n + 1) => F.obj f.left)
    (fun _ => F.map f.hom)]
  [∀ n : ℕ, PreservesLimit
    (WidePullbackShape.wideCospan f.right (fun _ : Fin (n + 1) => f.left)
      (fun _ => f.hom)) F]

local instance mappedArrowHasWidePullback :
    ∀ n : ℕ, HasWidePullback (Arrow.mk (F.map f.hom)).right
      (fun _ : Fin (n + 1) => (Arrow.mk (F.map f.hom)).left)
      (fun _ => (Arrow.mk (F.map f.hom)).hom) :=
  fun n => inferInstanceAs
    (HasWidePullback (F.obj f.right) (fun _ : Fin (n + 1) => F.obj f.left)
      (fun _ => F.map f.hom))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of each actual Čech term with the term of the image arrow. -/
def cechTermMapIso (n : ℕ) :
    F.obj (f.cechNerve.obj (op ⦋n⦌)) ≅
      (Arrow.mk (F.map f.hom)).cechNerve.obj (op ⦋n⦌) :=
  preservesLimitIso F _ ≪≫ HasLimit.isoOfNatIso (cechWideCospanCompIso F f n)

@[reassoc (attr := simp)]
theorem cechTermMapIso_hom_base (n : ℕ) :
    (cechTermMapIso F f n).hom ≫
      WidePullback.base (fun _ : Fin (n + 1) => F.map f.hom) =
        F.map (WidePullback.base (fun _ : Fin (n + 1) => f.hom)) := by
  simp [cechTermMapIso, WidePullback.base, cechWideCospanCompIso]

@[reassoc (attr := simp)]
theorem cechTermMapIso_hom_π (n : ℕ) (j : Fin (n + 1)) :
    (cechTermMapIso F f n).hom ≫
      WidePullback.π (fun _ : Fin (n + 1) => F.map f.hom) j =
        F.map (WidePullback.π (fun _ : Fin (n + 1) => f.hom) j) := by
  simp [cechTermMapIso, WidePullback.π, cechWideCospanCompIso]

/-- The termwise comparisons commute with all simplicial operators. -/
def cechNerveMapIso :
    f.cechNerve ⋙ F ≅ (Arrow.mk (F.map f.hom)).cechNerve :=
  NatIso.ofComponents (fun n => cechTermMapIso F f n.unop.len) (by
    intro n m g
    apply WidePullback.hom_ext
    · intro j
      simp only [Functor.comp_map, Category.assoc, cechTermMapIso_hom_π,
        Arrow.cechNerve_map, WidePullback.lift_π, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
        ← F.map_comp]
    · simp only [Functor.comp_map, Category.assoc, cechTermMapIso_hom_base,
        Arrow.cechNerve_map, WidePullback.lift_base, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
        ← F.map_comp])

/-- The simplicial comparison also respects the actual augmentations. -/
def augmentedCechNerveMapIso :
    (SimplicialObject.Augmented.whiskeringObj _ _ F).obj f.augmentedCechNerve ≅
      (Arrow.mk (F.map f.hom)).augmentedCechNerve :=
  Comma.isoMk (cechNerveMapIso F f) (Iso.refl _) (by
    ext n
    simp [cechNerveMapIso, Arrow.augmentedCechNerve, Arrow.mk_hom])

/-- A section after applying the limit-preserving functor contracts the mapped
augmented nerve. A section of the original arrow is not required. -/
def mappedCechExtraDegeneracy (S : SplitEpi (F.map f.hom)) :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((SimplicialObject.Augmented.whiskeringObj _ _ F).obj f.augmentedCechNerve) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (augmentedCechNerveMapIso F f).symm
    (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (F.map f.hom)) S)

end Langlands.Cohomology.SiteCech
