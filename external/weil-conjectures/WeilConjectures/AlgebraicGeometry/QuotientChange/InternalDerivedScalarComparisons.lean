/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.InternalDerivedScalarComparisons

/-! # Integral quotient scalar comparison for unbounded direct image

Positive quotient levels are indexed by n + 1. All categories are ordinary unbounded
derived categories of the recorded internal module objects. No completion is applied.

## References

* Stacks Project, Tags 093M, 0D6D, 0D6E, 07A6 and 0944
* Stacks 0D6D, 0G7E
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']












end AlgebraicGeometry.ProEtale.QuotientChange
namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']









end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']

/-- The ordinary balanced composition, including coefficient-map composition. -/
def ordinaryComp (a : Λ ⟶ Λ') [IsMonHom a]
    (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]
    (h : a ≫ b = c) (T : Scheme.{u}) :
    extension a T ⋙ extension b T ≅ extension c T :=
  by
    have hc : coefficientMap a T ≫ coefficientMap b T = coefficientMap c T :=
      (coefficientMap_comp a b T).symm.trans
        (congrArg (fun d ↦ coefficientMap d T) h)
    exact (Mod.extendScalarsComp (coefficientMap a T) (coefficientMap b T)).symm ≪≫
      (Mod.extendRestrictAdjunction _).leftAdjointUniq
        ((Mod.extendRestrictAdjunction _).ofNatIsoRight (Mod.comapCongr hc).symm)

/-- The universal-counit characterization of successive scalar balancing. On K-flat
representatives the ordinary comparison sends (x tensor s) tensor t to x tensor bar(s)t. -/
def SuccessiveNormalized (a : Λ ⟶ Λ') [IsMonHom a]
    (b : Λ' ⟶ Λ'') [IsMonHom b] (c : Λ ⟶ Λ'') [IsMonHom c]
    (h : a ≫ b = c) (T : Scheme.{u})
    (e : D a T ⋙ D b T ≅ D c T) : Prop :=
  ∀ P : HomotopyCategory (Modules Λ T) (.up ℤ),
    e.hom.app (DerivedCategory.Qh.obj P) ≫ (scalarCounit c T).app P =
      (D b T).map ((scalarCounit a T).app P) ≫
        (scalarCounit b T).app (((extension a T).mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (ordinaryComp a b c h T) (.up ℤ)).hom.app P)

end AlgebraicGeometry.ProEtale.QuotientChange
