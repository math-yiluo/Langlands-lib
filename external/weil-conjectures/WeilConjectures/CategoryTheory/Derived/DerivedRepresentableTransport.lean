/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.R.RHomDerivedRoof
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# Derived transport of represented functors

Source: Stacks Project, derived.tex, Tags 05TH, 05TI, 070I and 015F;
representability and coherence calculation in the DAG
(blueprint: lem-pur-derived-representable-transport).

The comparisons below use the left Kan extension unit, the exact termwise derived
functor, and the roof-normalized comparison of `exists_rhom_hom_derived_roof`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u₁ u₂ u₃ v w₁ w₂ w₃ wAb

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{wAb} AddCommGrpCat.{v}]

/-- The termwise transformation followed by the target derived unit and exact
localization comparison. Source: Stacks Tags 05TI and 015F
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportUnit
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus) :=
  whiskerRight (NatTrans.mapHomotopyCategoryPlus tau) DerivedCategory.Plus.Qh ≫
    whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ S'))).inv
      DerivedCategory.Plus.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft L.mapHomotopyCategoryPlus S'.rightDerivedFunctorPlusUnith ≫
    (associator _ _ _).inv ≫
    whiskerRight L.mapDerivedCategoryPlusFactorsh.inv S'.rightDerivedFunctorPlus ≫
    (associator _ _ _).hom

/-- The canonical comparison is the Kan factorization of `representableTransportUnit`.
Source: Stacks Tag 05TI (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportComparison
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
  S.rightDerivedFunctorPlus.rightDerivedDesc S.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) _ (representableTransportUnit L S S' tau)

/-- Apply the exact derived functor to a shifted morphism and precompose with `d⁻¹`.
The displayed single and shift isomorphisms are the termwise ones.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportHom
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P : A} {P' : B} (d : L.obj P ≅ P') (X : DerivedCategory.Plus A) (a : ℤ)
    (f : (DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :
    (DerivedCategory.singleFunctor B 0).obj P' ⟶
      (L.mapDerivedCategoryPlus.obj X).obj⟦a⟧ :=
  (DerivedCategory.singleFunctor B 0).map d.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫ L.mapDerivedCategory.map f ≫
    (L.mapDerivedCategory.commShiftIso a).hom.app X.obj

private lemma transport_fac
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlusUnith ≫
        whiskerLeft DerivedCategory.Plus.Qh (representableTransportComparison L S S' tau) =
      representableTransportUnit L S S' tau := by
  exact S.rightDerivedFunctorPlus.rightDerived_fac _ _ _ _

variable {C : Type u₃} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₃} C]

end CategoryTheory.Functor
