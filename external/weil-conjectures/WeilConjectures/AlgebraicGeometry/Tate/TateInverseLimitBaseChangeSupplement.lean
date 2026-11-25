/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement

/-!
# Base change of an inverse-limit tower and its finite tensor reduction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, final sentence;
Stacks Project, Tags 03DB, 03CO and 03EL
(blueprint: lem-pur-tate-inverse-limit-base-change).

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

attribute [local irreducible] proEtaleRingModulePullback proEtaleModuleInverseImage
  proEtaleRingModuleAdjunction

private abbrev tateRestrictedSectionModule
    (T : Scheme.{u}) {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y) ((ModuleCat.restrictScalars
      (((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

attribute [local instance] tateRestrictedSectionModule

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

private theorem tensorHomEquiv_apply (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (m : M.val.obj U) :
    (tensorHomEquiv T φ M H f).val.app U m =
      f.val.app U ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
          φ M).presheaf).app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) := by
  rfl

private theorem tensorHomEquiv_tmul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj R))
    (H : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj S))
    (f : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      s • (@id (H.val.obj U) ((tensorHomEquiv T φ M H f).val.app U m)) := by
  let k := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      S).obj) f
  change k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
    s • k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  let k' : (ModuleCat.extendScalars (φ.hom.app U).hom).obj (M.val.obj U) ⟶
      H.val.obj U := k.app U
  have hh := k'.hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at hh
  exact hh

-- Keep the tensor universal-property inverse folded after establishing its API.
-- Otherwise later equivalence comparisons unfold its sectionwise tensor construction.
attribute [local irreducible] restrictionToTensor

/-- The actual constant-coefficient module category.
Source: Stacks Tag 03DB (blueprint: lem-pur-tate-inverse-limit-base-change). -/
abbrev tateModules (T : Scheme.{u}) (R : Type u) [CommRing R] :=
  proEtaleRingModules T (proEtaleConstantRing T R)

/-- The constant sheaf map induced by a coefficient homomorphism.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateConstantMap (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : proEtaleConstantRing T R ⟶ proEtaleConstantRing T A :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom)))

/-- Restriction along the indicated constant coefficient map, with unchanged sections.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateRestrict (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) : tateModules T A ⥤ tateModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (tateConstantMap T f))

/-- The sheaf tensor `M ⊗_R A_T`, with its natural A-module structure.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTensor (T : Scheme.{u}) {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) : tateModules T A :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateConstantMap T f) M

/-- A pure tensor in the sheaf tensor, using the module sheafification unit.
Source: Stacks Tag 03EK (blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateTmul {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (M : tateModules T R) (U : T.ProEt)
    (a : (proEtaleConstantRing T A).obj.obj (op U)) (x : M.val.obj (op U)) :
    (tateTensor T f M).val.obj (op U) :=
  purScalarSection (proEtaleConstantRing T R) (proEtaleConstantRing T A)
    (tateConstantMap T f) M U a x

/-- Inverse image, transported through the stipulated canonical constant-ring isomorphism.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tatePullback {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] : tateModules T R ⥤ tateModules T' R :=
  proEtaleRingModulePullback h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))

/-- The canonical inverse-image unit on local module sections.
Source: Stacks Tags 03D2 and 09A5
(blueprint: lem-pur-tate-inverse-limit-base-change). -/
def tateUnit {T T' : Scheme.{u}} (h : T' ⟶ T) (R : Type u) [CommRing R]
    [IsIso (proEtaleCoefficientInverseImageMap h R)] (M : tateModules T R)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    ((tatePullback h R).obj M).val.obj (op ((proEtaleBaseChange h).obj U)) :=
  ((proEtaleRingModuleAdjunction h (proEtaleConstantRing T R) (proEtaleConstantRing T' R)
    (asIso (proEtaleCoefficientInverseImageMap h R))).unit.app M).val.app (op U) x

private def tensorUnit {T : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (a : R →+* A) (M : tateModules T R) :
    M ⟶ (tateRestrict T a).obj (tateTensor T a M) :=
  tensorHomEquiv T (tateConstantMap T a) M (tateTensor T a M) (𝟙 _)

private theorem tensorUnit_apply {T : Scheme.{u}} {R A : Type u}
    [CommRing R] [CommRing A] (a : R →+* A) (M : tateModules T R)
    (U : T.ProEt) (x : M.val.obj (op U)) :
    (tensorUnit a M).val.app (op U) x = tateTmul a M U 1 x := by
  rfl

attribute [local irreducible] tensorUnit

private def constantUnit (T : Scheme.{u}) (R : Type u) [CommRing R] :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} R)) ⟶
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing T R)).obj :=
  adicLisseConstantUnit T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallyInjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallyInjective T (ULift.{u + 1, u} R)

private instance (T : Scheme.{u}) (R : Type u) [CommRing R] :
    Presheaf.IsLocallySurjective (ProEt.topology T) (constantUnit T R) :=
  adicLisseConstantUnit_locallySurjective T (ULift.{u + 1, u} R)

attribute [local irreducible] tensorHomEquiv tensorPresheafHomEquiv tensorToRestriction

private theorem tateConstantMap_comp (T : Scheme.{u})
    {R Q A : Type u} [CommRing R] [CommRing Q] [CommRing A]
    (q : R →+* Q) (a : Q →+* A) :
    tateConstantMap T (a.comp q) = tateConstantMap T q ≫ tateConstantMap T a := by
  unfold tateConstantMap
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
private def reductionUnit {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F) :
    L ⟶ (tateRestrict T (a.comp q)).obj (tateTensor T a G) where
  val :=
    { app U := ModuleCat.ofHom
        (X := L.val.obj U)
        (Y := ((tateRestrict T (a.comp q)).obj (tateTensor T a G)).val.obj U)
        { toFun := fun x ↦ (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x))
          map_add' := by intros; simp only [map_add]
          map_smul' := by
            intro r x
            have hi := (i.inv.val.app U).hom.map_smul r (p.val.app U x)
            have hp := (p.val.app U).hom.map_smul r x
            have ht := ((tensorUnit a G).val.app U).hom.map_smul
              ((tateConstantMap T q).hom.app U r) (i.inv.val.app U (p.val.app U x))
            change (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U (r • x))) =
              (tateConstantMap T (a.comp q)).hom.app U r •
                (show (tateTensor T a G).val.obj U from
                  (tensorUnit a G).val.app U (i.inv.val.app U (p.val.app U x)))
            rw [tateConstantMap_comp]
            rw [hp, hi]
            exact ht }
      naturality := by
        intro U V f
        ext x
        exact (congrArg (fun y ↦ (tensorUnit a G).val.app V (i.inv.val.app V y))
          (PresheafOfModules.naturality_apply p.val f x)).trans
          ((congrArg (fun y ↦ (tensorUnit a G).val.app V y)
            (PresheafOfModules.naturality_apply i.inv.val f (p.val.app U x))).trans
            (PresheafOfModules.naturality_apply (tensorUnit a G).val f _)) }

private theorem reductionUnit_apply {T : Scheme.{u}} {R Q A : Type u}
    [CommRing R] [CommRing Q] [CommRing A] (q : R →+* Q) (a : Q →+* A)
    (L F : tateModules T R) (G : tateModules T Q)
    (i : (tateRestrict T q).obj G ≅ F) (p : L ⟶ F)
    (U : T.ProEt) (x : L.val.obj (op U)) :
    (reductionUnit q a L F G i p).val.app (op U) x =
      tateTmul a G U 1 (i.inv.val.app (op U) (p.val.app (op U) x)) := by
  exact tensorUnit_apply a G U _

attribute [local irreducible] reductionUnit

end AlgebraicGeometry.Scheme
