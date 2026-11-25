/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorBaseChange
import WeilConjectures.Topology.InverseImageRegularModule

/-! # The regular module of a ring-sheaf pushout

Source: Stacks Project, Morphisms, Tag 01SB, scalar-extension construction.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {U X : Scheme.{u}} (f : U ⟶ X)

private abbrev regularRingSheaf {T : TopCat.{u}} (S : T.Sheaf CommRingCat.{u}) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private def regularExtensionSection {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) (W : (TopologicalSpace.Opens T)ᵒᵖ) :
    (ModuleCat.extendScalars (t.hom.app W).hom).obj
      ((SheafOfModules.unit (regularRingSheaf A)).val.obj W) ≅
      (SheafOfModules.unit (regularRingSheaf B)).val.obj W := by
  letI := (t.hom.app W).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid (A.obj.obj W) (B.obj.obj W)
    (B.obj.obj W)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private theorem regularExtensionSection_tmul {T : TopCat.{u}}
    {A B : T.Sheaf CommRingCat.{u}} (t : A ⟶ B) (W : (TopologicalSpace.Opens T)ᵒᵖ)
    (z : B.obj.obj W) (a : A.obj.obj W) :
    (regularExtensionSection t W).hom (z ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] a) =
      z * t.hom.app W a := by
  let := (t.hom.app W).hom.toAlgebra
  change TensorProduct.AlgebraTensorModule.rid (A.obj.obj W) (B.obj.obj W) (B.obj.obj W)
    (z ⊗ₜ[A.obj.obj W] a) = _
  rw [TensorProduct.AlgebraTensorModule.rid_tmul]
  change t.hom.app W a * z = _
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private def regularExtensionPresheafIso {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) :
    SheafOfModules.changeOfRingsPresheaf.{u, u, u} t (SheafOfModules.unit (regularRingSheaf A)) ≅
      (SheafOfModules.unit (regularRingSheaf B)).val := by
  refine PresheafOfModules.isoMk (regularExtensionSection t) ?_
  intro W W' i
  apply ModuleCat.ExtendScalars.hom_ext
  intro a
  change (regularExtensionSection t W').hom
    (SheafOfModules.changeOfRingsMap t (SheafOfModules.unit (regularRingSheaf A)) i
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] a)) =
    B.obj.map i ((regularExtensionSection t W).hom
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] a))
  rw [show SheafOfModules.changeOfRingsMap t (SheafOfModules.unit (regularRingSheaf A)) i
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] a) =
      (B.obj.map i 1) ⊗ₜ[A.obj.obj W', (t.hom.app W').hom] (A.obj.map i a) from
    Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap t
      (SheafOfModules.unit (regularRingSheaf A)) i) 1 a]
  rw [map_one, regularExtensionSection_tmul, regularExtensionSection_tmul, one_mul, one_mul]
  exact ConcreteCategory.congr_hom (t.hom.naturality i) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private def regularExtensionIso {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) :
    SheafOfModules.changeOfRings.{u, u, u} t (SheafOfModules.unit (regularRingSheaf A)) ≅
      SheafOfModules.unit (regularRingSheaf B) :=
  (PresheafOfModules.sheafification (𝟙 (regularRingSheaf B).obj)).mapIso
    (regularExtensionPresheafIso t) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).counit.app
      (SheafOfModules.unit (regularRingSheaf B)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private theorem regularExtensionIso_formula {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) (W : (TopologicalSpace.Opens T)ᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t
      (SheafOfModules.unit (regularRingSheaf A))).obj W) :
    (regularExtensionIso t).hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t
          (SheafOfModules.unit (regularRingSheaf A)))).app W x) =
      (regularExtensionSection t W).hom x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)
  let Q := SheafOfModules.unit (regularRingSheaf B)
  let q := (regularExtensionPresheafIso t).hom
  have hn := congrArg (fun a ↦ a.app W x) (adj.unit_naturality q)
  have hc (y : Q.val.obj W) :=
    congrArg (fun a ↦ a.app W y) (adj.right_triangle_components Q)
  change (adj.counit.app Q).val.app W
    (((PresheafOfModules.sheafification (𝟙 (regularRingSheaf B).obj)).map q).val.app W
      ((adj.unit.app _).app W x)) = _
  exact (congrArg ((adj.counit.app Q).val.app W) hn).trans
    (hc ((regularExtensionSection t W).hom x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private def changeOfRingsIso {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) {M N : SheafOfModules.{u} (regularRingSheaf A)} (q : M ≅ N) :
    SheafOfModules.changeOfRings.{u, u, u} t M ≅
      SheafOfModules.changeOfRings.{u, u, u} t N := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M ≅
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N :=
    PresheafOfModules.isoMk (fun W ↦
      (ModuleCat.extendScalars (t.hom.app W).hom).mapIso
        ((PresheafOfModules.evaluation (regularRingSheaf A).obj W).mapIso
          ((SheafOfModules.forget (regularRingSheaf A)).mapIso q)))
      (by
        intro W W' i
        exact SheafOfModules.changeOfRingsHom_naturality t M q.hom i)
  exact (PresheafOfModules.sheafification (𝟙 (regularRingSheaf B).obj)).mapIso p

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private theorem changeOfRingsIso_formula {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) {M N : SheafOfModules.{u} (regularRingSheaf A)} (q : M ≅ N)
    (W : (TopologicalSpace.Opens T)ᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M).obj W) :
    (changeOfRingsIso t q).hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M)).app W x) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N)).app W
      ((ModuleCat.extendScalars (t.hom.app W).hom).map (q.hom.val.app W) x) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N :=
    { app := fun W ↦ (ModuleCat.extendScalars (t.hom.app W).hom).map (q.hom.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality t M q.hom }
  exact congrArg (fun a ↦ a.app W x)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).unit_naturality p)

open scoped ChangeOfRings in
private abbrev extensionTensor {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) (M : SheafOfModules.{u} (regularRingSheaf A))
    (W : (TopologicalSpace.Opens T)ᵒᵖ) (z : B.obj.obj W) (m : M.val.obj W) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M).obj W :=
  z ⊗ₜ[A.obj.obj W, (t.hom.app W).hom] m

local instance instHasLeftKanExtension_pushoutRegularModuleComparison
    : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
    (Opens.map f.base).op.HasLeftKanExtension F := fun F ↦ by
  have : (Opens.map f.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
  exact Functor.HasLeftKanExtension.mk _
    (Functor.pointwiseLeftKanExtensionUnit (Opens.map f.base).op F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The regular module of the pushout algebra is the tensor pullback of the direct
image of the regular structure module, compatibly with the pullback unit.
Source: Stacks Project, Morphisms, Tag 01SB, construction of h; Modules, Tag 008A.
(blueprint: stage3-pushout-regular-module-comparison).

Proof: Write A = f_*O_U and restrict its regular module along O_X → A. This is
literally the module pushforward of O_U. Apply affine_module_tensor_baseChange
(which does not assume affineness) to the regular A-module. Inverse image of the
regular A-module is the regular inverse-image algebra module: the inverse-image
unit commutes with addition and multiplication; uniqueness of extensions of
these operations identifies the scalar action. Extension of this module along
IA → B is the regular B-module. On the tensor presheaf the two maps are
z tensor a ↦ z*t(a) and z ↦ z tensor 1. Balancing and the unit laws show they
are inverse and B-linear, and naturality gives inverse maps after sheafification.
Restrict scalars along b and compose this isomorphism with the cancellation
isomorphism. Its unit formula sends the module pullback unit of d to
1*t(η(d)) = δ(d). No affine hypothesis is needed for this sheaf-level comparison.
The zero algebra and empty open cause no exception: the same formulas and
balanced tensor identities apply. -/
theorem exists_pushout_regularModule_comparison
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t) :
    ∃ e : (tensorPullback f).obj
        ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf)) ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map b)).obj
          (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
      ∀ (V : X.Opens) (d : Γ(U, f ⁻¹ᵁ V)),
        e.hom.val.app (op (f ⁻¹ᵁ V))
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
            ((pushforward f).obj (SheafOfModules.unit U.ringCatSheaf))).val.app (op V) d) =
          (t.hom.app (op (f ⁻¹ᵁ V))).hom
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map f.base) CommRingCat.{u} (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology U)).unit.app
                ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf)).hom.app
                  (op V) d) := by
  classical
  let A := (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
  let G := SheafOfModules.unit (regularRingSheaf A)
  let ρ : X.sheaf ⟶ A := ⟨f.c⟩
  let S := SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map ρ)
  obtain ⟨P, pobj, κ, _, hκ⟩ := affine_module_tensor_baseChange f B b t hpushout
  obtain ⟨q, hq⟩ := TopCat.Sheaf.exists_inverseImage_regularModule_iso f.base A
  let c := changeOfRingsIso t q ≪≫ regularExtensionIso t
  let Rb := SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map b)
  let e := (κ.app G).symm ≪≫ Rb.mapIso (eqToIso (pobj G) ≪≫ c)
  refine ⟨e, ?_⟩
  intro V d
  let W := op (f ⁻¹ᵁ V)
  let m := ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) AddCommGrpCat.{u} (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology U)).unit.app
      ((SheafOfModules.toSheaf (regularRingSheaf A)).obj G)).hom.app (op V) d
  have h := hκ G (op V) d
  change c.hom.val.app W
    ((eqToHom (pobj G)).val.app W
      ((κ.inv.app G).val.app W
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (S.obj G)).val.app (op V) d))) = _
  refine (congrArg (fun x ↦ c.hom.val.app W x) h).trans ?_
  change (regularExtensionIso t).hom.val.app W
    ((changeOfRingsIso t q).hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (regularRingSheaf B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t
          (TopCat.Sheaf.inverseImageModule f.base A G))).app W
        (extensionTensor t (TopCat.Sheaf.inverseImageModule f.base A G) W 1 m))) = _
  refine (congrArg (fun x ↦ (regularExtensionIso t).hom.val.app W x)
    (changeOfRingsIso_formula t q W _)).trans ?_
  refine (regularExtensionIso_formula t W _).trans ?_
  have ht :
      (ModuleCat.extendScalars (t.hom.app W).hom).map (q.hom.val.app W)
        (extensionTensor t (TopCat.Sheaf.inverseImageModule f.base A G) W 1 m) =
      extensionTensor t
        (SheafOfModules.unit (regularRingSheaf (TopCat.Sheaf.inverseImageRing f.base A)))
        W 1 (q.hom.val.app W m) := by
    exact ModuleCat.ExtendScalars.map_tmul _ _ _ _
  refine (congrArg (fun x ↦ (regularExtensionSection t W).hom x) ht).trans ?_
  refine (regularExtensionSection_tmul t W 1 (q.hom.val.app W m)).trans ?_
  exact (one_mul _).trans (congrArg (t.hom.app W) (hq (op V) d))

end
end AlgebraicGeometry.Scheme.Modules
