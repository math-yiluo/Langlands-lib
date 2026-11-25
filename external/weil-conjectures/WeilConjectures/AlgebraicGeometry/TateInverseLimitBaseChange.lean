/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso

set_option linter.privateModule false

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(auxiliary; not a blueprint node).

The index `op r` denotes the positive level `r + 1`. Scalar extension is the
recorded sheaf tensor construction, with its pure tensors written in the order `a ⊗ x`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

-- The universe-polymorphic `{max u (t + 1)}` sheafification instances get stuck on
-- universe constraints for the `CommRingCat.{u + 1}` sheaves of this file.
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective

attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction

section

private local instance tateInverseLimitBaseChangeRestrictedModule (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars
        (((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj.map i).hom).obj
        (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMapMixedUniverses.{u, u + 1, u + 1,
    u + 1} c M i) s m

end

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
      CommRingCat.{u + 1}
      RingCat.{u + 1})).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (X := M.val.obj Y) (Y := H.val.obj Y) (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (X := M.val.obj X) (Y := H.val.obj X) (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (X := M.val.obj W) (Y := H.val.obj W) (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂
        CommRingCat.{u + 1}
        RingCat.{u + 1})).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom (X := M.val.obj W) (Y := H.val.obj W)).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj A)) (H : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u
        + 1} RingCat.{u
        + 1})).map c)).obj H) :=
  (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
    (P := SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} c M)
    (F := H)).trans (tensorPresheafHomEquiv T c M H)

attribute [local irreducible] restrictionToTensor

private def constantUnit (T : Scheme.{u}) (R : Type u) [CommRing R] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} R)) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T R)).obj :=
  adicLisseConstantUnit T (ULift.{u + 1, u} R)

private instance tateInverseLimitBaseChangeInst1 (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallyInjective T (ULift.{u + 1, u} R)

private instance tateInverseLimitBaseChangeInst2 (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallySurjective T (ULift.{u + 1, u} R)

attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction

attribute [local irreducible] exchangeModuleComposition

end AlgebraicGeometry.Scheme
