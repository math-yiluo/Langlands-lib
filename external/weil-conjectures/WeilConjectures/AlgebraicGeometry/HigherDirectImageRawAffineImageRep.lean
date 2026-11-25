/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverNaturality
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Affine raw classes in the image of a stage

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: sbc-lem-higher-image-raw-affine-image-rep).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

attribute [local irreducible] higherDirectImageRawOverPullback
  higherDirectImageOverMap higherDirectImagePresheafToSheaf upperStar lowerStar
  DerivedCategory.Plus.homologyFunctor DerivedCategory.Plus.singleFunctors

set_option backward.isDefEq.respectTransparency true in
/-- A raw cohomology class on an affine etale object has the same associated
higher-image section as a raw class at one stage. This says nothing about arbitrary
higher-image sections, sheaf colimits, or the injectivity of the comparison.
Source: Stacks Project, Tag 09Z1, the cohomology colimit in the proof; Tag 0EZM.
(blueprint: sbc-lem-higher-image-raw-affine-image-rep).

Proof: The existing raw complex presentation identifies the raw diagram and
cocone with a uniformly bounded-below abelian etale complex system on the
base-changed inverse system. Its isColimit consequence applies complex
continuity in every integer degree. The forgetful functor from abelian groups
to types preserves this filtered colimit, so the raw class z is the image of a
class t at one stage. The existing raw-over pullback comparison identifies the
section of that raw image with the section obtained from t by the canonical
higher-image transition. Apply the limit raw-to-sheaf component to the raw
representative equality, and compose the resulting equality with this canonical
comparison. This proves the displayed section equality. No directed final
reindexing, sheafification descent or separate negative-degree argument is needed. -/
theorem exists_higher_image_raw_affine_image_rep
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (z : (higherDirectImageRawOverPresheaf Λ k G q c.pt).obj (op U)) :
    ∃ (i : I)
      (t : (higherDirectImageRawOverPresheaf Λ k G q (D.obj i)).obj (op U)),
      ((higherDirectImageOverMap Λ k G q (c.π.app i)).hom.app (op U))
        ((higherDirectImageRawOverComparison Λ k G q (D.obj i)).app (op U) t) =
      (higherDirectImageRawOverComparison Λ k G q c.pt).app (op U) z := by
  have s := nonempty_higherDirectImageRaw_complex_presentation Λ k G q D c hc U
  obtain ⟨hB⟩ := s.isColimit
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget AddCommGrpCat.{u + 1})
  obtain ⟨i, t, ht⟩ := Concrete.isColimit_exists_rep
    (higherDirectImageRawDiagram Λ k G q D U) hB z
  dsimp only [higherDirectImageRawDiagram, Functor.comp_obj, Functor.op_obj,
    higherDirectImageRawOverFunctor] at t
  have ht' := (higherDirectImageRawOverPullbackHom_apply Λ k G q
    (c.π.app i.unop) U t).symm.trans ht
  refine ⟨i.unop, t, ?_⟩
  exact (higherDirectImageRawOverPullback_comparison Λ k G q
    (A := c.pt) (B := D.obj i.unop) (c.π.app i.unop) U t).symm.trans
    (congrArg ((higherDirectImageRawOverComparison Λ k G q c.pt).app (op U)) ht')

end AlgebraicGeometry.Etale
