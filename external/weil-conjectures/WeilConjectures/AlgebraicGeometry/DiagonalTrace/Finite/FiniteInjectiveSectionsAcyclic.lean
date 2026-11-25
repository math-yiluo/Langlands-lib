/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! Universe transport for finite-module injective acyclicity.
(blueprint: lem-sfb-finite-injective-sections-acyclic). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

theorem finiteInjective_sections_acyclic (T : Scheme.{u}) (m : ℕ)
    (I : SheafOfModules.{u + 1}
      (SemilinearSections.ring.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T m))) [Injective I] :
    (sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
      (evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 T)))).rightAcyclic ((finiteForget l E T m).obj I) := by
  let J := Scheme.ProEt.topology T
  let R := SemilinearSections.ring.{u + 1, u, u + 1} J (SpTowerShriek.B l E T m)
  let C' := ULiftHom.{u + 1} T.ProEt
  let down : C' ⥤ T.ProEt := ULiftHom.down
  let up : T.ProEt ⥤ C' := ULiftHom.up
  let J' := down.inducedTopology J
  have : down.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : T.ProEt ≌ C').inverse.IsEquivalence)
  have : up.IsEquivalence :=
    inferInstanceAs ((ULiftHom.equiv : T.ProEt ≌ C').functor.IsEquivalence)
  have : down.IsContinuous J' J := by dsimp [J', down]; infer_instance
  have : up.IsContinuous J J' :=
    inferInstanceAs ((ULiftHom.equiv : T.ProEt ≌ C').functor.IsContinuous J
      ((ULiftHom.equiv : T.ProEt ≌ C').inverse.inducedTopology J))
  have : (ULiftHom.equiv.symm : C' ≌ T.ProEt).functor.IsContinuous J' J :=
    inferInstanceAs (down.IsContinuous J' J)
  have : (ULiftHom.equiv.symm : C' ≌ T.ProEt).inverse.IsContinuous J J' :=
    inferInstanceAs (up.IsContinuous J J')
  let R' := (down.sheafPushforwardContinuous RingCat.{u + 1} J' J).obj R
  let E' : SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} R' :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (ULiftHom.equiv.symm : C' ≌ T.ProEt) (𝟙 R') (𝟙 R)
      (by ext V x; change (R.obj.map (𝟙 _)).hom x = x; simp)
      (by ext V x; change (R'.obj.map (𝟙 _)).hom x = x; simp)
  let I' := E'.functor.obj I
  have : Injective I' := (E'.map_injective_iff I).mpr inferInstance
  have : (ULiftHom.equiv.symm : C' ≌ T.ProEt).inverse.IsDenseSubsite J J' := by
    exact inferInstanceAs ((ULiftHom.equiv : T.ProEt ≌ C').functor.IsDenseSubsite J
      ((ULiftHom.equiv : T.ProEt ≌ C').inverse.inducedTopology J))
  let B := ((ULiftHom.equiv.symm : C' ≌ T.ProEt).sheafCongr
    J' J AddCommGrpCat.{u + 1}).symm
  let V := B.functor
  have : V.Additive := by constructor; intro M N f g; ext W; rfl
  let W := Scheme.ProEt.mk (𝟙 T)
  let F := sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
    (evaluation T.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)
  let F' := sheafToPresheaf J' AddCommGrpCat.{u + 1} ⋙
    (evaluation C'ᵒᵖ AddCommGrpCat.{u + 1}).obj (op (up.obj W))
  have hV (M : Sheaf J AddCommGrpCat.{u + 1}) [Injective M] :
      F'.rightAcyclic (V.obj M) := by
    have : Injective (V.obj M) := (B.map_injective_iff M).mpr inferInstance
    exact F'.rightAcyclic_of_injective _
  have eF : F ≅ V ⋙ F' := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let : HasExt.{u + 1} (Sheaf J' AddCommGrpCat.{u + 1}) := hasExt_of_enoughInjectives _
  intro q
  let : Subsingleton (Sheaf.H' ((SheafOfModules.toSheaf R').obj I') (q + 1)
      (up.obj W)) := injective_module_abelian_acyclic (up.obj W) I' (q + 1) (by omega)
  obtain ⟨d⟩ := Sheaf.nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    J' (up.obj W) (q + 1)
  have hz' : IsZero (Sheaf.H' ((SheafOfModules.toSheaf R').obj I') (q + 1)
      (up.obj W)) := AddCommGrpCat.isZero_of_subsingleton _
  have hz : IsZero ((F'.rightDerived (q + 1)).obj
      ((SheafOfModules.toSheaf R').obj I')) :=
    hz'.of_iso (d.app ((SheafOfModules.toSheaf R').obj I')).symm
  have hobj : (SheafOfModules.toSheaf R').obj I' ≅
      V.obj ((SheafOfModules.toSheaf R).obj I) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  exact (hz.of_iso ((F'.rightDerived (q + 1)).mapIso hobj).symm).of_iso
    (Functor.rightDerivedObjIsoOfIso eF (q + 1) _ ≪≫
      Functor.compRightDerivedObjIso V F' hV (q + 1) _)

end AlgebraicGeometry.ProEtale.DiagonalTrace
