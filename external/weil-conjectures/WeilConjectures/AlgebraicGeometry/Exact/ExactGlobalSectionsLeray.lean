/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-! # Leray on a base with exact global sections

Source: Stacks Project, Tags 03Q9 and 03QO, derived-functor composition.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Exact global sections commute with homology; derived composition then gives Leray.
Source: Stacks Project, Tags 03Q9 and 03QO
(blueprint: def-weil-pbc-exact-global-sections-leray). -/
noncomputable def exactGlobalSectionsLerayHomologyIso {Y T : Scheme.{v}}
    (h : PreservesFiniteColimits (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (t : Y ⟶ T) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})) :
    (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} t).obj K)) ≅
    (cohomology AddCommGrpCat.{v + 1} Y q).obj (DerivedCategory.Plus.ι.obj K) :=
  haveI := h
  (Functor.mapDerivedCategoryPlusHomologyFunctorIso
      (Sheaf.Γ T.smallEtaleTopology
        AddCommGrpCat.{v + 1}) q).app
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1}
        t).obj K) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((Sheaf.Γ T.smallEtaleTopology
        AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).symm.app _) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((Sheaf.Γ T.smallEtaleTopology
        AddCommGrpCat.{v + 1}).rightDerivedFunctorPlusCompatibility.app _) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedGlobalSections AddCommGrpCat.{v + 1}
        T).mapIso
        ((Functor.rightDerivedFunctorPlusCompatibility
          (lowerStar AddCommGrpCat.{v + 1}
            t)).app K)) ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        t).app
        (DerivedCategory.Plus.ι.obj K))

end AlgebraicGeometry.Etale
