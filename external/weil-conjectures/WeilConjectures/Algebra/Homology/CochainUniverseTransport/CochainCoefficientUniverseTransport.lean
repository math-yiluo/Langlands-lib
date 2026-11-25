/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Sites.SheafOfTypes

import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Canonical coefficient and module size transport

Source: Stacks, Modules on Sites, 03DA and 03EK, using the invariance of
sheaf conditions and balanced tensors under sectionwise isomorphism
(blueprint: def-pur-cochain-coefficient-universe-transport).

All carriers below are explicitly ULift, all restrictions apply the original
restriction to ULift.down, and all scalars act through ULift.down. In particular
this construction does not equate site, ring, or module universes.
-/

@[expose] public section
universe uC vC r m w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules.CochainUniverseTransport
set_option autoImplicit false
set_option linter.checkUnivs false

/-- Ring-universe transport is the usual sectionwise ULift ring functor.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
def ringFunctor : CommRingCat.{r} ⥤ CommRingCat.{max r m w} where
  obj A := CommRingCat.of (ULift.{max m w} A)
  map f := CommRingCat.ofHom f.hom.ulift

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

private theorem commRing_isSheaf_of_forget (P : Cᵒᵖ ⥤ CommRingCat.{z})
    (hP : Presheaf.IsSheaf J (P ⋙ CategoryTheory.forget CommRingCat)) :
    Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit] at hP ⊢
  intro X S hS
  obtain ⟨h⟩ := hP S hS
  let F := S.arrows.diagram.op ⋙ P
  let : HasLimit (F ⋙ CategoryTheory.forget CommRingCat) := ⟨_, h⟩
  let : Small.{z} (F ⋙ CategoryTheory.forget CommRingCat).sections :=
    (Types.hasLimit_iff_small_sections _).1 inferInstance
  let : HasLimit F := inferInstance
  let : ReflectsLimit F (CategoryTheory.forget CommRingCat) :=
    reflectsLimit_of_reflectsIsomorphisms F _
  exact ⟨isLimitOfReflects (CategoryTheory.forget CommRingCat) h⟩

/-- Sectionwise ring lifting preserves the sheaf condition.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: matching families lift and descend componentwise through ULift.up/down.
Apply the original unique gluing axiom and lift the resulting section. The ring
operations are transported by the same bijections. -/
@[instance]
theorem ringFunctor_hasSheafCompose : J.HasSheafCompose (ringFunctor.{r, m, w}) := by
  constructor
  intro P hP
  apply commRing_isSheaf_of_forget
  apply (isSheaf_iff_isSheaf_of_type J _).2
  change Presieve.IsSheaf J ((P ⋙ CategoryTheory.forget CommRingCat) ⋙ uliftFunctor)
  apply Presieve.isSheaf_comp_uliftFunctor
  exact (isSheaf_iff_isSheaf_of_type J _).1
    (Presheaf.isSheaf_comp_of_isSheaf J P (CategoryTheory.forget CommRingCat) hP)

/-- The genuinely constructed coefficient ring in the common ambient universe.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
abbrev ring (R : Sheaf J CommRingCat.{r}) : Sheaf J CommRingCat.{max r m w} :=
  (sheafCompose J (ringFunctor.{r, m, w})).obj R

/-- Forgetting a lifted commutative ring to a ring preserves sheaves.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: the forgetful functor creates limits, so it preserves the matching-family
limit expressing the sheaf condition. -/
@[instance]
theorem liftedRingForgetHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{z} RingCat.{z}) := by
  constructor
  intro P hP
  rw [Presheaf.isSheaf_iff_isLimit] at hP ⊢
  intro X S hS
  obtain ⟨h⟩ := hP S hS
  let F := S.arrows.diagram.op ⋙ P
  let : HasLimit F := ⟨_, h⟩
  let : HasLimit (F ⋙ CategoryTheory.forget CommRingCat) := by infer_instance
  let : Small.{z} (F ⋙ CategoryTheory.forget CommRingCat).sections :=
    (Types.hasLimit_iff_small_sections _).1 inferInstance
  let : Small.{z}
      ((F ⋙ forget₂ CommRingCat RingCat) ⋙ CategoryTheory.forget RingCat).sections := by
    change Small.{z} (F ⋙ CategoryTheory.forget CommRingCat).sections
    infer_instance
  let : PreservesLimit F (forget₂ CommRingCat RingCat) :=
    preservesLimit_of_preserves_limit_cone (CommRingCat.limitConeIsLimit F)
      (RingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat RingCat))
  exact ⟨isLimitOfPreserves (forget₂ CommRingCat RingCat) h⟩

variable (R : Sheaf J CommRingCat.{r})

/-- Original module sheaves, retaining their independent carrier universe m.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
abbrev OriginalModules := ringedSiteModules.{m}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The lifted scalar acts by its down-map on the lifted module carrier.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable instance moduleAction (M : OriginalModules.{uC, vC, r, m} R) (U : Cᵒᵖ) :
    Module ((ring.{uC, vC, r, m, w} R).obj.obj U)
      (ULift.{max r w} (M.val.obj U)) :=
  letI : Module (R.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule
  inferInstanceAs (Module (ULift.{max m w} (R.obj.obj U))
    (ULift.{max r w} (M.val.obj U)))

/-- Lift a local restriction, applying the original map to the descended section.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleMap (M : OriginalModules.{uC, vC, r, m} R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U) (ULift.{max r w} (M.val.obj U)) ⟶
      (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).obj
        (ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj V) (ULift.{max r w} (M.val.obj V))) :=
  ModuleCat.ofHom
    (X := ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U)
      (ULift.{max r w} (M.val.obj U)))
    (Y := (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).obj
      (ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj V)
        (ULift.{max r w} (M.val.obj V))))
    { toFun := fun x ↦ ULift.up (M.val.map f x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (M.val.map f).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (M.val.map_smul f a.down x.down) }

/-- Functoriality of lifted restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: evaluate on ULift.up(x), descend, and use the original identity and
composition equations. ULift.up/down are inverse functions. -/
theorem moduleMap_laws (M : OriginalModules.{uC, vC, r, m} R) :
    (∀ U : Cᵒᵖ, moduleMap.{uC, vC, r, m, w} R M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (((ring.{uC, vC, r, m, w} R).obj ⋙
        forget₂ CommRingCat RingCat).map (𝟙 U)).hom
          (congrArg RingCat.Hom.hom (((ring.{uC, vC, r, m, w} R).obj ⋙
            forget₂ CommRingCat RingCat).map_id U))).inv.app _) ∧
    (∀ {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
      moduleMap.{uC, vC, r, m, w} R M (f ≫ g) = moduleMap.{uC, vC, r, m, w} R M f ≫
        (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).map
          (moduleMap.{uC, vC, r, m, w} R M g) ≫
        (ModuleCat.restrictScalarsComp' ((ring.{uC, vC, r, m, w} R).obj.map f).hom
          ((ring.{uC, vC, r, m, w} R).obj.map g).hom ((ring.{uC, vC, r, m, w} R).obj.map (f ≫
            g)).hom
          (congrArg RingCat.Hom.hom (((ring.{uC, vC, r, m, w} R).obj ⋙
            forget₂ CommRingCat RingCat).map_comp f g))).inv.app _) := by
  constructor
  · intro U
    ext x
    change ULift.up (M.val.map (𝟙 U) x.down) = x
    have h := congrArg (fun k ↦ k x.down) (M.val.map_id U)
    change M.val.map (𝟙 U) x.down = x.down at h
    cases x
    exact congrArg ULift.up h
  · intro U V W f g
    ext x
    exact congrArg ULift.up (M.val.map_comp_apply f g x.down)

/-- The lifted module presheaf, with explicit ULift carriers and restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def modulePresheaf (M : OriginalModules.{uC, vC, r, m} R) :
    PresheafOfModules.{max r m w}
      (((ring.{uC, vC, r, m, w} R).obj ⋙ forget₂ CommRingCat RingCat)) where
  obj U := ModuleCat.of ((ring.{uC, vC, r, m, w} R).obj.obj U) (ULift.{max r w} (M.val.obj U))
  map := moduleMap.{uC, vC, r, m, w} R M
  map_id := (moduleMap_laws.{uC, vC, r, m, w} R M).1
  map_comp := (moduleMap_laws.{uC, vC, r, m, w} R M).2

/-- The explicitly lifted abelian presheaf is a sheaf.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: forget the transported action. The presheaf is the original abelian
presheaf followed by ULift. Unique gluing transports through ULift.up/down. -/
theorem modulePresheaf_isSheaf (M : OriginalModules.{uC, vC, r, m} R) :
    Presheaf.IsSheaf J (modulePresheaf.{uC, vC, r, m, w} R M).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (CategoryTheory.forget AddCommGrpCat)
  apply (isSheaf_iff_isSheaf_of_type J _).2
  change Presieve.IsSheaf J ((M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) ⋙ uliftFunctor)
  apply Presieve.isSheaf_comp_uliftFunctor
  exact (isSheaf_iff_isSheaf_of_type J _).1
    (Presheaf.isSheaf_comp_of_isSheaf J _ (CategoryTheory.forget AddCommGrpCat) M.isSheaf)

/-- The genuinely constructed module sheaf in the common ambient universe.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def module (M : OriginalModules.{uC, vC, r, m} R) :
    ringedSiteModules.{max r m w}
      ((sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj (ring.{uC, vC,
        r, m, w} R)) :=
  ⟨modulePresheaf.{uC, vC, r, m, w} R M, modulePresheaf_isSheaf.{uC, vC, r, m, w} R M⟩

/-- Lift a module homomorphism by its explicit sectionwise ULift formula.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleHomComponent {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N) (U :
  Cᵒᵖ) :
    (module.{uC, vC, r, m, w} R M).val.obj U ⟶ (module.{uC, vC, r, m, w} R N).val.obj U :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up (h.val.app U x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (h.val.app U).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (map_smul (h.val.app U).hom a.down x.down) }

/-- Lifted homomorphisms commute with restrictions.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: descend a section and use the original morphism's naturality, then lift. -/
theorem moduleHomComponent_naturality {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (module.{uC, vC, r, m, w} R M).val.map f ≫
        (ModuleCat.restrictScalars ((ring.{uC, vC, r, m, w} R).obj.map f).hom).map
          (moduleHomComponent.{uC, vC, r, m, w} R h V) =
      moduleHomComponent.{uC, vC, r, m, w} R h U ≫ (module.{uC, vC, r, m, w} R N).val.map f := by
  ext x
  exact congrArg ULift.up (PresheafOfModules.naturality_apply h.val f x.down)

/-- The explicitly lifted morphism of module sheaves.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def moduleHom {M N : OriginalModules.{uC, vC, r, m} R} (h : M ⟶ N) :
    module.{uC, vC, r, m, w} R M ⟶ module.{uC, vC, r, m, w} R N :=
  ⟨{ app := moduleHomComponent.{uC, vC, r, m, w} R h, naturality :=
    moduleHomComponent_naturality.{uC, vC, r, m, w} R h }⟩

/-- The sectionwise lift is functorial on module homomorphisms.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport).
Proof: identities and compositions act on ULift.up(x) by the corresponding
original maps. Extensionality of module sheaf maps gives the equations. -/
theorem moduleHom_laws :
    (∀ M : OriginalModules.{uC, vC, r, m} R, moduleHom.{uC, vC, r, m, w} R (𝟙 M) = 𝟙 _) ∧
      (∀ (M N H : OriginalModules.{uC, vC, r, m} R) (f : M ⟶ N) (g : N ⟶ H),
        moduleHom.{uC, vC, r, m, w} R (f ≫ g) = moduleHom.{uC, vC, r, m, w} R f ≫ moduleHom.{uC,
          vC, r, m, w} R g) := by
  constructor
  · intro M
    ext U x
    rfl
  · intro M N H f g
    ext U x
    rfl

/-- Canonical common-universe embedding; every carrier and every map is explicit.
Source: Stacks 03DA
(blueprint: def-pur-cochain-coefficient-universe-transport). -/
noncomputable def functor : OriginalModules.{uC, vC, r, m} R ⥤ ringedSiteModules.{max r m w}
    ((sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj (ring.{uC, vC, r,
      m, w} R)) where
  obj := module.{uC, vC, r, m, w} R
  map := moduleHom.{uC, vC, r, m, w} R
  map_id := (moduleHom_laws.{uC, vC, r, m, w} R).1
  map_comp := (moduleHom_laws.{uC, vC, r, m, w} R).2 _ _ _

private theorem sheafificationHomEquiv_isIso
    (S : Sheaf J RingCat.{z}) [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P : PresheafOfModules.{w} S.obj} {F : SheafOfModules.{w} S}
    (d : P ⟶ (PresheafOfModules.restrictScalars (𝟙 S.obj)).obj F.val)
    (hd : J.W ((PresheafOfModules.toPresheaf _).map d)) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv.{w} (𝟙 S.obj)).symm d) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{w} S)).1
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
    Adjunction.homEquiv_counit]
  have := (J.W_iff _).1 hd
  infer_instance

-- Lift a bilinear map without unfolding the surrounding sheaf constructions.
private noncomputable def liftTensorMap {A : Type r} [CommRing A]
    {X Y Z : Type m} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module A X] [Module A Y] [Module A Z] (η : TensorProduct A X Y →ₗ[A] Z) :
    TensorProduct (ULift.{max m w} A) (ULift.{max r w} X) (ULift.{max r w} Y)
      →ₗ[ULift.{max m w} A] ULift.{max r w} Z := by
  apply TensorProduct.lift
  refine
    { toFun := fun x ↦
        { toFun := fun y ↦ ULift.up (η (x.down ⊗ₜ[A] y.down))
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro y z
    exact congrArg ULift.up (by
      change η (_ ⊗ₜ[A] (y.down + z.down)) = _
      rw [TensorProduct.tmul_add, map_add])
  · intro a y
    exact congrArg ULift.up (by
      change η (_ ⊗ₜ[A] (a.down • y.down)) = _
      rw [TensorProduct.tmul_smul (R' := A), map_smul]
      rfl)
  · intro x z
    apply LinearMap.ext
    intro y
    exact congrArg ULift.up (by
      change η ((x.down + z.down) ⊗ₜ[A] y.down) =
        η (x.down ⊗ₜ[A] y.down) + η (z.down ⊗ₜ[A] y.down)
      rw [TensorProduct.add_tmul, map_add])
  · intro a x
    apply LinearMap.ext
    intro y
    exact congrArg ULift.up (by
      change η ((a.down • x.down) ⊗ₜ[A] y.down) = a.down • η (x.down ⊗ₜ[A] y.down)
      rw [← TensorProduct.smul_tmul' (R' := A), map_smul])

private noncomputable def tensorDownComponent
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) (U : Cᵒᵖ) :
    TensorProduct ((ring.{uC, vC, r, m, w} R).obj.obj U)
      ((module.{uC, vC, r, m, w} R M).val.obj U)
      ((module.{uC, vC, r, m, w} R N).val.obj U) →ₗ[(ring.{uC, vC, r, m, w} R).obj.obj U]
      (module.{uC, vC, r, m, w} R ((siteSheafTensorRight N).obj M)).val.obj U :=
  liftTensorMap.{r, m, w}
    (((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) (𝟙 _)).unit.app
        (siteTensorPresheaf M.val N.val)).app U).hom

private noncomputable def tensorDown
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    ((module.{uC, vC, r, m, w} R M).val ⊗
      (module.{uC, vC, r, m, w} R N).val) ⟶
      (module.{uC, vC, r, m, w} R ((siteSheafTensorRight N).obj M)).val where
  app U := ModuleCat.ofHom
    (X := (((module.{uC, vC, r, m, w} R M).val ⊗
      (module.{uC, vC, r, m, w} R N).val)).obj U)
    (Y := (module.{uC, vC, r, m, w} R ((siteSheafTensorRight N).obj M)).val.obj U)
    (tensorDownComponent.{uC, vC, r, m, w} R M N U)
  naturality := by
    intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact congrArg ULift.up
      (PresheafOfModules.naturality_apply
        ((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
          (𝟙 _)).unit.app (siteTensorPresheaf M.val N.val)) f
          (x.down ⊗ₜ[R.obj.obj U] y.down))

-- The sectionwise tensor equivalence is compatible with every restriction.
private noncomputable def tensorPresheafLiftIso
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    (siteTensorPresheaf M.val N.val).presheaf ⋙ AddCommGrpCat.uliftFunctor.{max r w, m} ≅
      (((module.{uC, vC, r, m, w} R M).val ⊗
        (module.{uC, vC, r, m, w} R N).val)).presheaf := by
  refine NatIso.ofComponents (fun U ↦
    (TensorProduct.AlgebraTensorModule.uliftEquiv (R.obj.obj U) (R.obj.obj U)
      (M.val.obj U) (N.val.obj U)).toAddEquiv.toAddCommGrpIso) ?_
  intro U V f
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  rcases x with ⟨x⟩
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
      have ha : (ULift.up (x + y) : ULift.{max r w} _) = ULift.up x + ULift.up y := rfl
      simpa only [ha, map_add] using congrArg₂ (· + ·) hx hy

private theorem tensorDown_factor
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    (tensorPresheafLiftIso.{uC, vC, r, m, w} R M N).hom ≫
      (PresheafOfModules.toPresheaf _).map (tensorDown.{uC, vC, r, m, w} R M N) =
    Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction
        (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
        (𝟙 _)).unit.app (siteTensorPresheaf M.val N.val)))
      AddCommGrpCat.uliftFunctor.{max r w, m} := by
  ext U x
  rcases x with ⟨x⟩
  induction x using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy =>
      have ha : (ULift.up (x + y) : ULift.{max r w} _) = ULift.up x + ULift.up y := rfl
      simpa only [ha, map_add] using congrArg₂ (· + ·) hx hy

private theorem ulift_preservesSheafification
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{max r w, m} := by
  constructor
  intro P Q f hf
  have hi := hf.isLocallyInjective
  have hs := hf.isLocallySurjective
  have : Presheaf.IsLocallyInjective J
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor |>.map f) := by
    constructor
    intro U x y h
    apply J.superset_covering _
      (Presheaf.equalizerSieve_mem J f x.down y.down (congrArg ULift.down h))
    intro V i hi
    exact congrArg ULift.up hi
  have : Presheaf.IsLocallySurjective J
      ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor |>.map f) := by
    constructor
    intro U x
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.down)
    intro V i hi
    obtain ⟨y, hy⟩ := hi
    exact ⟨ULift.up y, congrArg ULift.up hy⟩
  exact J.W_of_isLocallyBijective _

-- The tensor map is the lifted sheafification unit, up to the tensor equivalence.
private theorem tensorDown_W
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (tensorDown.{uC, vC, r, m, w} R M N)) := by
  let : J.PreservesSheafification AddCommGrpCat.uliftFunctor.{max r w, m} :=
    ulift_preservesSheafification.{uC, vC, r, m, w}
  have h := J.W_of_preservesSheafification AddCommGrpCat.uliftFunctor.{max r w, m}
    _ (J.W_toSheafify (siteTensorPresheaf M.val N.val).presheaf)
  change J.W (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
      (𝟙 _)).unit.app (siteTensorPresheaf M.val N.val)))
        AddCommGrpCat.uliftFunctor.{max r w, m}) at h
  rw [← tensorDown_factor.{uC, vC, r, m, w} R M N] at h
  exact (J.W.cancel_left_of_respectsIso _ _).1 h

private noncomputable def tensorDescent
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    (PresheafOfModules.sheafification.{max r m w}
      (R := (sheafCompose J (forget₂ CommRingCat.{max r m w} RingCat.{max r m w})).obj
        (ring.{uC, vC, r, m, w} R)) (𝟙 _)).obj
      ((module.{uC, vC, r, m, w} R M).val ⊗
        (module.{uC, vC, r, m, w} R N).val) ⟶
      module.{uC, vC, r, m, w} R ((siteSheafTensorRight N).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    (tensorDown.{uC, vC, r, m, w} R M N)

private theorem tensorDescent_isIso
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    IsIso (tensorDescent.{uC, vC, r, m, w} R M N) := by
  let : HasSheafify J AddCommGrpCat.{max r m w} := hasSheafify_coefficientUniverse
  exact sheafificationHomEquiv_isIso _ _ (tensorDown_W.{uC, vC, r, m, w} R M N)

private noncomputable def tensorComparison
    [EssentiallySmall.{max r m w} C]
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
    (M N : OriginalModules.{uC, vC, r, m} R) :
    module.{uC, vC, r, m, w} R M ⊗ module.{uC, vC, r, m, w} R N ≅
      module.{uC, vC, r, m, w} R ((siteSheafTensorRight N).obj M) := by
  have := tensorDescent_isIso.{uC, vC, r, m, w} R M N
  exact tensorObjIsoSheafification (module.{uC, vC, r, m, w} R M)
    (module.{uC, vC, r, m, w} R N) ≪≫
    asIso (tensorDescent.{uC, vC, r, m, w} R M N)

end SheafOfModules.CochainUniverseTransport
