/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-! # Finitely presented local constant models on the pro-etale site

## References

* Stacks Project, Tags 09AJ and 093U
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open Opposite

private noncomputable def fixedModelSchemeIso {X : Scheme.{u}}
    {B : Type (u + 1)} [CommRing B]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B)) (U : X.ProEt)
    (M : ModuleCat.{u + 1} B) :
    (F.over U ≅ (constantSheaf ((ProEt.topology X).over U) _).obj M) ≃
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).obj F ≅
        (constantSheaf (ProEt.topology U.left) _).obj M) := by
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology U.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  let E := (ProEt.sliceEquiv X U).sheafCongr
    ((ProEt.topology X).over U) (ProEt.topology U.left) (ModuleCat.{u + 1} B)
  let r : E.functor.obj (F.over U) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} B) U.hom).obj F :=
    (ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))) ≪≫
      ((ProEtale.upperStarIsoLocalizationRestriction _ U.hom U.prop).app F).symm
  let c := ((ProEt.sliceEquiv X U).constantSheafSheafCongrIso
    ((ProEt.topology X).over U) (ProEt.topology U.left)
    (ModuleCat.{u + 1} B) (Over.mkIdTerminal (X := U))).app M
  exact
    { toFun := fun e ↦ r.symm ≪≫ E.functor.mapIso e ≪≫ c
      invFun := fun e ↦ E.functor.preimageIso (r ≪≫ e ≪≫ c.symm)
      left_inv := by intro e; apply Iso.ext; apply E.functor.map_injective; simp [r, c]
      right_inv := by intro e; apply Iso.ext; simp }

private noncomputable def fixedConstantPullbackIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B) :
    (ProEtale.upperStar (ModuleCat.{u + 1} B) f).obj
        ((constantSheaf (ProEt.topology Y) _).obj M) ≅
      (constantSheaf (ProEt.topology X) _).obj M :=
  (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} B))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange f) _
      (ProEt.topology Y) (ProEt.topology X)).symm).app M ≪≫
    ((proEtaleBaseChange f).constantSheafsheafPullbackIso (ModuleCat.{u + 1} B)
      (ProEt.topology Y) (ProEt.topology X) (ProEt.isTerminalMkId Y)
      ((ProEt.isTerminalMkId Y).isTerminalObj (proEtaleBaseChange f) _)).app M

end AlgebraicGeometry.Scheme
