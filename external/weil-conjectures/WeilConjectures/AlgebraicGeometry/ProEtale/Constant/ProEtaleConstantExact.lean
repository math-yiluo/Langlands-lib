/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteConstantCoefficientTransport

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

/-!
# Exact pullback of finite constant pro-etale left modules

The coefficient categories are the recorded continuous-function ringed module categories.
The small-model module Kan extension gives inverse image over the inverse-image ring;
restriction along the inverse of the canonical coefficient map transports the action.
The commutative comparison uses the recorded tensor pullback, with the canonical
constant-preserving coefficient identifications written explicitly.

## References

* Stacks Project, Tags 00WJ, 03D2, and 04JC
* Stacks Tags 00W1 and 00YV
* Stacks Tags 0H7J and 09A5
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end AlgebraicGeometry.Scheme
end

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Register the recorded coefficient isomorphism, without choosing any new map. -/
noncomputable instance finiteCoefficientInverseImageMap_invertible :
    IsIso (finiteCoefficientInverseImageMap f Λ) :=
  finiteCoefficientInverseImageMap_isIso.{u} f Λ

/-- The inverse-image coefficient ring on the original small site. -/
noncomputable abbrev finiteCoefficientInverseRing :=
  (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj (finiteCoefficientRingSheaf V Λ)

/-- The ring adjunction unit on the small site models. Only the Hom universe is enlarged. -/
noncomputable def finiteCoefficientModelRingUnit :
    ((AsSmall.down : Scheme.proEtaleSiteModel V ⥤ V.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (Scheme.proEtaleModelTopology V) (Scheme.ProEt.topology V)).obj
        (finiteCoefficientRingSheaf V Λ) ⟶
    ((Scheme.proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.proEtaleModelTopology V) (Scheme.proEtaleModelTopology U)).obj
        (((AsSmall.down : Scheme.proEtaleSiteModel U ⥤ U.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.proEtaleModelTopology U) (Scheme.ProEt.topology U)).obj
            (finiteCoefficientInverseRing f Λ)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
      (finiteCoefficientRingSheaf V Λ)).hom)⟩

/-- Inverse image of left modules over the inverse-image ring. Mathlib's module pullback
is the module Kan extension followed by sheafification, along the actual ring unit.
Its action is the inverse image of the original action under the product comparison.
Transport to and from the equivalent small model retains every original site object. -/
noncomputable def finiteCoefficientModuleInverseImage :
    FiniteCoefficientModules V Λ ⥤ SheafOfModules.{u + 1} (finiteCoefficientInverseRing f Λ) :=
  Scheme.proEtaleModuleToModel (finiteCoefficientRingSheaf V Λ) ⋙
    SheafOfModules.pullback (finiteCoefficientModelRingUnit f Λ) ⋙
    Scheme.proEtaleModuleFromModel (finiteCoefficientInverseRing f Λ)

/-- The specified pullback: transport the inverse-image action by c_f inverse.
Thus r acts as c_f inverse(r), and on underlying abelian maps the functor is inverse image.
No tensor product or multiplicative commutativity is required here. -/
noncomputable def finiteCoefficientModulePullback :
    FiniteCoefficientModules V Λ ⥤ FiniteCoefficientModules U Λ :=
  finiteCoefficientModuleInverseImage f Λ ⋙
    SheafOfModules.restrictScalars (inv (finiteCoefficientInverseImageMap f Λ))


section
open Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
open Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
end

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Compatibility of the commutative presentation with ring sheafification.
This supplies the construction obligation of the canonical coefficient comparison below. -/
theorem finiteCoefficientCommRing_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  StrictTower.constantRingForget_preservesSheafification.{u} T

attribute [instance] finiteCoefficientCommRing_preservesSheafification

set_option linter.unusedSectionVars false in
/-- The canonical commutative coefficient map is invertible too. -/
theorem finiteCoefficientCommRingMap_isIso :
    IsIso (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.defeqAttrib.useBackward true in
  let G := Scheme.proEtaleBaseChange f
  let hV : IsTerminal (⊤_ V.ProEt) := terminalIsTerminal
  let hU := hV.isTerminalObj G _
  let aV := constantSheafAdj (Scheme.ProEt.topology V) CommRingCat.{u + 1} hV
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  let a := (aV.comp adj).ofNatIsoRight (Iso.refl _)
  let b := constantSheafAdj (Scheme.ProEt.topology U) CommRingCat.{u + 1} hU
  let e := a.leftAdjointUniq b
  have he : Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of Λ) = e.hom.app (CommRingCat.of Λ) := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.refl_hom,
      NatTrans.id_app, Category.comp_id, Adjunction.comp_homEquiv]
    dsimp [Scheme.proEtaleConstantInverseImageMap]
    rw [← Adjunction.homEquiv_counit]
    dsimp only [adj]
    rw [Equiv.apply_symm_apply]
    dsimp only [Scheme.proEtaleConstantDirectImageMap, aV, constantSheafAdj]
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hV).homEquiv _ _
      (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
        _ _)
        (((sheafificationAdjunction (Scheme.ProEt.topology V) CommRingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

attribute [instance] finiteCoefficientCommRingMap_isIso

section
open Scheme
set_option backward.isDefEq.respectTransparency false in
private noncomputable def finiteTensorModelEquivalence (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≌
      SheafOfModules.{u + 1} A := by
  let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)

private noncomputable def finiteTensorScalarEquivalence (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) RingCat.{u + 1}} (rc : A ≅ B) :
    SheafOfModules.{u + 1} B ≌ SheafOfModules.{u + 1} A := by
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  let : (CategoryTheory.Equivalence.refl (C := X.ProEt)).inverse.IsContinuous
      (ProEt.topology X) (ProEt.topology X) := by
    change (𝟭 X.ProEt).IsContinuous _ _
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (J := ProEt.topology X) (K := ProEt.topology X) (S := A) (R := B)
    (CategoryTheory.Equivalence.refl (C := X.ProEt)) rc.hom rc.inv
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [B.obj.map_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.inv_hom_id.symm)
    (by
      apply NatTrans.ext
      funext U
      dsimp [CategoryTheory.Equivalence.refl]
      erw [A.obj.map_id, Category.comp_id]
      exact congrArg (fun q ↦ q.hom.app U) rc.hom_inv_id)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteTensorAdjunction :
    finiteCoefficientModulePullback f Λ ⊣
      SheafOfModules.pushforward (finiteCoefficientDirectImageMap f Λ) := by
  let A := finiteCoefficientRingSheaf V Λ
  let B := finiteCoefficientInverseRing f Λ
  let eV := finiteTensorModelEquivalence V A
  let eU := finiteTensorModelEquivalence U B
  let a₀ := eV.symm.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction
      (finiteCoefficientModelRingUnit f Λ)).comp eU.toAdjunction)
  let a₁ := (finiteTensorScalarEquivalence U
    (asIso (finiteCoefficientInverseImageMap f Λ))).symm.toAdjunction
  let a := a₀.comp a₁
  change finiteCoefficientModulePullback f Λ ⊣ _ at a
  apply a.ofNatIsoRight
  let ρ := (proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app A ≫
    (proEtaleSheafDirectImage f RingCat.{u + 1}).map (finiteCoefficientInverseImageMap f Λ)
  have hρ : ρ = finiteCoefficientDirectImageMap f Λ := by
    exact ((proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  refine (NatIso.ofComponents (fun M ↦ ?_) ?_) ≪≫ SheafOfModules.pushforwardCongr hρ
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
  · intro M N g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    rfl
end

end AlgebraicGeometry.ProEtale
