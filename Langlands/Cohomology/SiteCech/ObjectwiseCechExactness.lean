import Langlands.Cohomology.SiteCech.CechEvaluation
import Mathlib.CategoryTheory.Types.Basic

/-! # Objectwise surjective free Čech augmentations -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w u₁ v₁ u₂ v₂

section Additive

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : A ⥤ D) [F.Additive] (X : SimplicialObject.Augmented A)

/-- Applying an additive functor to the actual augmentation agrees, via the
complex and single-object comparisons, with augmenting the mapped object. -/
def augmentationMapArrowIso :
    Arrow.mk ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X)) ≅
    Arrow.mk (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ _ F).obj X)) :=
  Arrow.isoMk
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app X.left)
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app X.right)
    (by
      ext n
      cases n with
      | zero =>
        simp [HomologicalComplex.singleMapHomologicalComplex,
          AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso]
      | succ n => simp)

/-- Quasi-isomorphism of the mapped actual augmentation can be checked on the
augmentation of the mapped simplicial object. -/
theorem quasiIso_map_augmentation_iff :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (AlgebraicTopology.AlternatingFaceMapComplex.ε.app X)) ↔
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj _ _ F).obj X)) :=
  _root_.quasiIso_iff_of_arrow_mk_iso _ _ (augmentationMapArrowIso F X)

end Additive

section Presheaf

variable {C : Type u} [Category.{v} C]
variable (R : Type w) [CommRing R]

/-- The objectwise free module presheaf functor. -/
def freeModulePresheafFunctor : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ ModuleCat.{w} R) :=
  (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/-- The objectwise free module augmented Čech nerve. -/
def freePresheafAugmentedCechNerve (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ ModuleCat.{w} R) :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (freeModulePresheafFunctor R)).obj
    f.augmentedCechNerve

/-- The chain complex of the objectwise free module Čech nerve. -/
def freePresheafCechChainComplex (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    ChainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (freePresheafAugmentedCechNerve R f).left

/-- The actual augmentation of the free module presheaf Čech complex. -/
def freePresheafCechAugmentation (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    freePresheafCechChainComplex R f ⟶
      (ChainComplex.single₀ _).obj ((freeModulePresheafFunctor R).obj f.right) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (freePresheafAugmentedCechNerve R f)

/-- A surjective evaluated arrow has a set-theoretic section. -/
def evaluationSplitEpi (f : Arrow (Cᵒᵖ ⥤ Type w)) (U : Cᵒᵖ)
    (h : Function.Surjective (f.hom.app U)) : SplitEpi (f.hom.app U) where
  section_ := TypeCat.ofHom (Function.surjInv h)
  id := by
    ext x
    exact Function.rightInverse_surjInv h x

/-- Objectwise surjectivity contracts the evaluated free module nerve. -/
def evaluatedFreePresheafCechExtraDegeneracy (f : Arrow (Cᵒᵖ ⥤ Type w)) (U : Cᵒᵖ)
    (h : Function.Surjective (f.hom.app U)) :
    SimplicialObject.Augmented.ExtraDegeneracy
      ((SimplicialObject.Augmented.whiskeringObj _ _
        ((evaluation Cᵒᵖ (ModuleCat.{w} R)).obj U)).obj
        (freePresheafAugmentedCechNerve R f)) :=
  (mappedCechExtraDegeneracy ((evaluation Cᵒᵖ (Type w)).obj U) f
    (evaluationSplitEpi f U h)).map (ModuleCat.free R)

/-- The actual free module presheaf Čech augmentation of an objectwise
surjective arrow is a quasi-isomorphism. -/
theorem quasiIso_freePresheafCechAugmentation_of_surjective
    (f : Arrow (Cᵒᵖ ⥤ Type w)) (h : ∀ U, Function.Surjective (f.hom.app U)) :
    QuasiIso (freePresheafCechAugmentation R f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro U
  apply (quasiIso_map_augmentation_iff
    ((evaluation Cᵒᵖ (ModuleCat.{w} R)).obj U)
    (freePresheafAugmentedCechNerve R f)).2
  exact (evaluatedFreePresheafCechExtraDegeneracy R f U (h U)).homotopyEquiv.quasiIso_hom

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]

/-- Exact sheafification carries objectwise free Čech exactness to the actual
free sheaf Čech augmentation. -/
theorem quasiIso_freeCechAugmentation_of_objectwise_surjective
    (f : Arrow (Cᵒᵖ ⥤ Type w)) (h : ∀ U, Function.Surjective (f.hom.app U)) :
    QuasiIso (freeCechAugmentation J R f) := by
  have := quasiIso_freePresheafCechAugmentation_of_surjective R f h
  exact (quasiIso_map_augmentation_iff (presheafToSheaf J (ModuleCat.{w} R))
    (freePresheafAugmentedCechNerve R f)).1
      (HomologicalComplex.quasiIso_map_of_preservesHomology
        (freePresheafCechAugmentation R f) (presheafToSheaf J (ModuleCat.{w} R)))

end Presheaf

end Langlands.Cohomology.SiteCech
