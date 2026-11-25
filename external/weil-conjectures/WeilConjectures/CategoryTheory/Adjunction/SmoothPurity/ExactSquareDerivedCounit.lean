/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Counits in an exact square of derived adjunctions

Source: Stacks Project, Derived Categories, Tags 09T5 and 070Y; exact-square extraction
of tower normalization, steps 6--8 (blueprint: lem-weil-pbc-exact-square-derived-counit).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uA uAp uB uBp vA vAp vB vBp wA wAp wB wBp

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {Ap : Type uAp} {B : Type uB} {Bp : Type uBp}
  [Category.{vA} A] [Category.{vAp} Ap] [Category.{vB} B] [Category.{vBp} Bp]
  [Abelian A] [Abelian Ap] [Abelian B] [Abelian Bp]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wAp} Ap]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wBp} Bp]

/-- The Hom formula specifying the derived adjunction on the fixed functors and fixed
right-derived unit, for every chain map. Source: Stacks Tag 09T5, with Tag 070Y
(blueprint: lem-weil-pbc-exact-square-derived-counit). -/
def Adjunction.HasExactDerivedHomFormula
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG) : Prop :=
  ∀ (M : CochainComplex B ℤ) (I : CochainComplex A ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj M ⟶ I),
    d.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj I)
        (F.mapDerivedCategoryFactors.hom.app M ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv M I f) ≫ η.app I

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

-- Adjoining a contractible summand makes a resolution monomorphic without changing
-- its homotopy type. No degreewise injectivity or enough-injectives assumption is used.
private theorem normalizedCounit
    (F : B ⥤ A) (G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (RG : DerivedCategory A ⥤ DerivedCategory B)
    (η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (d : F.mapDerivedCategory ⊣ RG)
    (hd : Adjunction.HasExactDerivedHomFormula F G adj RG η d)
    (I : CochainComplex A ℤ) :
    F.mapDerivedCategory.map (η.app I) ≫ d.counit.app (DerivedCategory.Q.obj I) =
      F.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have he := hd _ I ((adj.mapHomologicalComplex (.up ℤ)).counit.app I)
  have hid : (adj.mapHomologicalComplex (.up ℤ)).homEquiv _ I
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) = 𝟙 _ :=
    (adj.mapHomologicalComplex (.up ℤ)).right_triangle_components I
  rw [hid,
    DerivedCategory.Q.map_id, Category.id_comp] at he
  have he' := congrArg (d.homEquiv _ _).symm he
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply] using he'.symm

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem squareFactors
    (Fp : Bp ⥤ Ap) (F : B ⥤ A) (r : Ap ⥤ A) (s : Bp ⥤ B)
    [Fp.Additive] [F.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits Fp] [PreservesFiniteColimits Fp]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (hF : Fp ⋙ r = s ⋙ F) (K : CochainComplex Bp ℤ) :
    (Functor.mapDerivedCategorySquareIso (eqToIso hF)).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app ((s.mapHomologicalComplex (.up ℤ)).obj K) =
      r.mapDerivedCategory.map (Fp.mapDerivedCategoryFactors.hom.app K) ≫
        r.mapDerivedCategoryFactors.hom.app ((Fp.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (eqToIso hF) (.up ℤ)).hom.app K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fp r).inv.app
    (DerivedCategory.Q.obj K))).mp
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

end CategoryTheory
