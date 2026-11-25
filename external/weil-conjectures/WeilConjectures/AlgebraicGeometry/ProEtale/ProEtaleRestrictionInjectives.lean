/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# Pro-etale restriction preserves injectives

## References

* Stacks Project, small-site localization and derived sections
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The sectionwise comparison evaluates restriction at the identity of `W`.
Its components are the sheaf maps along the canonical identity-underlying-scheme
isomorphism from `W` to the image of that terminal object under composition with `W.hom`. -/
noncomputable def proEtaleLocalizationSectionsIso {X : Scheme.{u}} (W : X.ProEt)
    (Λ : Type (u + 1)) [Ring Λ] :
    ProEtale.sectionsFunctor (ModuleCat.{u + 1} Λ) W ≅
      ProEtale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop ⋙
        ProEtale.globalSectionsFunctor (ModuleCat.{u + 1} Λ) W.left :=
  let e : W ≅ (MorphismProperty.Over.map ⊤ W.prop).obj
      (MorphismProperty.Over.mk ⊤ (𝟙 W.left) (MorphismProperty.id_mem _ W.left)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op)
    (fun φ ↦ (φ.hom.naturality e.inv.op).symm)

end AlgebraicGeometry
