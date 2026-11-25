/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-!
# The explicit scalar-extension map on internal duals

Source: Stacks Project, Tags 03EK, 03EM, 04TT.
(blueprint: lem-sp-scalar-extension-dual-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
set_option hygiene false in
local notation:max "Mod" R:arg =>
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
set_option hygiene false in
local notation:max "𝒪" R:arg => unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- scalarDual_section_ext: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
theorem scalarDual_section_ext {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ)
    (φ ψ : (homObj (changeOfRingsOfUniverses α N) (𝒪 S)).val.obj U)
    (h : ∀ (W : (Over U.unop)ᵒᵖ) (t : S.obj.obj (op W.unop.left))
      (x : N.val.obj (op W.unop.left)),
      φ.app W (scalarExtensionSection α N (op W.unop.left) t x) =
        ψ.app W (scalarExtensionSection α N (op W.unop.left) t x)) : φ = ψ := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let η := scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)
  apply (𝒪 S).isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map η) z)
  intro V i hi
  obtain ⟨t, ht⟩ := hi
  change η.app (op V) t = (changeOfRingsOfUniverses α N).val.map i.op z at ht
  let k : Over.mk (i ≫ W.unop.hom) ⟶ W.unop := Over.homMk i
  have hp := PresheafOfModules.naturality_apply φ k.op z
  have hq := PresheafOfModules.naturality_apply ψ k.op z
  change (𝒪 S).val.map i.op (φ.app W z) = (𝒪 S).val.map i.op (ψ.app W z)
  refine hp.symm.trans (Eq.trans ?_ hq)
  change φ.app (op (Over.mk (i ≫ W.unop.hom)))
      ((changeOfRingsOfUniverses α N).val.map i.op z) =
    ψ.app (op (Over.mk (i ≫ W.unop.hom)))
      ((changeOfRingsOfUniverses α N).val.map i.op z)
  rw [← ht]
  clear ht
  have hη : φ.app (op (Over.mk (i ≫ W.unop.hom))) (η.app (op V) t) =
      ψ.app (op (Over.mk (i ≫ W.unop.hom))) (η.app (op V) t) := by
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [map_add, ht, ht']
    | tmul a x => exact h (op (Over.mk (i ≫ W.unop.hom))) a x
  exact hη

/-- scalarDualRawSection: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
noncomputable def scalarDualRawSection {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) (φ : (homObj N (𝒪 R)).val.obj U) :
    (PresheafOfModules.restrictOver S.obj U.unop).obj
        (changeOfRingsPresheafOfUniverses α N) ⟶
      (PresheafOfModules.restrictOver S.obj U.unop).obj (𝒪 S).val where
  app W := (ModuleCat.extendScalars (α.hom.app (op W.unop.left)).hom).map (φ.app W) ≫
    (scalarExtensionUnitRawIso α).hom.app (op W.unop.left)
  naturality := by
    intro W V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s x =>
      change S.obj.obj (op W.unop.left) at s
      change (scalarExtensionUnitRawIso α).hom.app (op V.unop.left)
        (((ModuleCat.extendScalars (α.hom.app (op V.unop.left)).hom).map (φ.app V))
          (changeOfRingsMapOfUniverses α N i.unop.left.op
            (s ⊗ₜ[R.obj.obj (op W.unop.left),
              (α.hom.app (op W.unop.left)).hom] x))) = _
      rw [changeOfRingsMap_tmulOfUniverses]
      dsimp only [Functor.comp_obj, Functor.op_obj] at *
      change α.hom.app (op V.unop.left) (φ.app V (N.val.map i.unop.left.op x)) *
          S.obj.map i.unop.left.op s =
        S.obj.map i.unop.left.op (α.hom.app (op W.unop.left) (φ.app W x) * s)
      rw [map_mul]
      erw [PresheafOfModules.naturality_apply φ i]
      exact congrArg (· * S.obj.map i.unop.left.op s)
        (ConcreteCategory.congr_hom (α.hom.naturality i.unop.left.op) _)

/-- scalarDualSliceUnit: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
noncomputable def scalarDualSliceUnit {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) :=
  (PresheafOfModules.restrictOver S.obj U.unop).map
    (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N))

/-- scalarDualSliceUnit_locallyInjective: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
instance scalarDualSliceUnit_locallyInjective {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) :
    PresheafOfModules.IsLocallyInjective (J.over U.unop) (scalarDualSliceUnit α N U) :=
  Presheaf.isLocallyInjective_whisker (J.over U.unop) J (Over.forget U.unop)
    ((PresheafOfModules.toPresheaf _).map
      (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)))

/-- scalarDualSliceUnit_locallySurjective: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
instance scalarDualSliceUnit_locallySurjective {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) :
    PresheafOfModules.IsLocallySurjective (J.over U.unop) (scalarDualSliceUnit α N U) :=
  Presheaf.isLocallySurjective_whisker (J.over U.unop) J (Over.forget U.unop)
    ((PresheafOfModules.toPresheaf _).map
      (scalarSheafificationUnit (changeOfRingsPresheafOfUniverses α N)))

/-- scalarDualBaseSection: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
noncomputable def scalarDualBaseSection
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) (φ : (homObj N (𝒪 R)).val.obj U) :
    (homObj (changeOfRingsOfUniverses α N) (𝒪 S)).val.obj U :=
  (PresheafOfModules.homEquivOfIsLocallyBijective (f := scalarDualSliceUnit α N U)
    ((𝒪 S).over U.unop).isSheaf).symm (scalarDualRawSection α N U φ)

/-- scalarDualBaseSection_tmul: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
theorem scalarDualBaseSection_tmul
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (N : Mod R) (U : Cᵒᵖ) (φ : (homObj N (𝒪 R)).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (t : S.obj.obj (op W.unop.left))
    (x : N.val.obj (op W.unop.left)) :
    (scalarDualBaseSection α N U φ).app W
        (scalarExtensionSection α N (op W.unop.left) t x) =
      α.hom.app (op W.unop.left) (φ.app W x) * t := by
  have h := congrArg (fun f ↦ f.app W
    (t ⊗ₜ[R.obj.obj (op W.unop.left), (α.hom.app (op W.unop.left)).hom] x))
      ((PresheafOfModules.homEquivOfIsLocallyBijective
        (f := scalarDualSliceUnit α N U) ((𝒪 S).over U.unop).isSheaf).apply_symm_apply
          (scalarDualRawSection α N U φ))
  exact h

/-- scalarDualBaseMap: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
noncomputable def scalarDualBaseMap
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R) :
    homObj N (𝒪 R) ⟶
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        (homObj (changeOfRingsOfUniverses α N) (𝒪 S)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom (Y :=
        (((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
          (homObj (changeOfRingsOfUniverses α N) (𝒪 S))).val.obj U))
        { toFun := scalarDualBaseSection α N U
          map_add' := by
            intro φ ψ
            apply scalarDual_section_ext α N U
            intro W t x
            change (scalarDualBaseSection α N U (φ + ψ)).app W
                (scalarExtensionSection α N (op W.unop.left) t x) =
              (scalarDualBaseSection α N U φ).app W
                (scalarExtensionSection α N (op W.unop.left) t x) +
              (scalarDualBaseSection α N U ψ).app W
                (scalarExtensionSection α N (op W.unop.left) t x)
            rw [scalarDualBaseSection_tmul, scalarDualBaseSection_tmul,
              scalarDualBaseSection_tmul]
            dsimp only [Functor.comp_obj, Functor.op_obj] at *
            change α.hom.app (op W.unop.left)
                ((show R.obj.obj (op W.unop.left) from φ.app W x) +
                  (show R.obj.obj (op W.unop.left) from ψ.app W x)) * t = _
            rw [map_add, add_mul]
            rfl
          map_smul' := by
            intro a φ
            apply scalarDual_section_ext α N U
            intro W t x
            change (scalarDualBaseSection α N U (a • φ)).app W
                (scalarExtensionSection α N (op W.unop.left) t x) =
              ((α.hom.app U a) • scalarDualBaseSection α N U φ).app W
                (scalarExtensionSection α N (op W.unop.left) t x)
            rw [scalarDualBaseSection_tmul]
            dsimp only [Functor.comp_obj, Functor.op_obj] at *
            change α.hom.app (op W.unop.left)
                (R.obj.map W.unop.hom.op a *
                  (show R.obj.obj (op W.unop.left) from φ.app W x)) * t =
              S.obj.map W.unop.hom.op (α.hom.app U a) *
                (show S.obj.obj (op W.unop.left) from (scalarDualBaseSection α N U φ).app W
                  (scalarExtensionSection α N (op W.unop.left) t x))
            rw [scalarDualBaseSection_tmul, map_mul, mul_assoc]
            exact congrArg (· * (α.hom.app (op W.unop.left) (φ.app W x) * t))
              (ConcreteCategory.congr_hom (α.hom.naturality W.unop.hom.op) a) }
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro φ
        apply scalarDual_section_ext α N V
        intro W t x
        change (scalarDualBaseSection α N V
            ((homObj N (𝒪 R)).val.map i φ)).app W
              (scalarExtensionSection α N (op W.unop.left) t x) =
          (scalarDualBaseSection α N U φ).app (op ((Over.map i.unop).obj W.unop))
              (scalarExtensionSection α N (op W.unop.left) t x)
        rw [scalarDualBaseSection_tmul]
        exact (scalarDualBaseSection_tmul α N U φ
          (op ((Over.map i.unop).obj W.unop)) t x).symm }

/-- scalarExtensionDualMap: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
noncomputable def scalarExtensionDualMap
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R) :
    changeOfRingsOfUniverses α (homObj N (𝒪 R)) ⟶
      homObj (changeOfRingsOfUniverses α N) (𝒪 S) :=
  scalarExtensionLift.{uC, vC, u, max uC vC u} α
    (homObj N (𝒪 R)) _ (scalarDualBaseMap α N)

/-- scalarExtensionDualMap_tmul: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
theorem scalarExtensionDualMap_tmul
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R)
    (U : Cᵒᵖ) (s t : S.obj.obj U) (φ : (homObj N (𝒪 R)).val.obj U)
    (x : N.val.obj U) :
    (((scalarExtensionDualMap α N).val.app U
        (scalarExtensionSection α (homObj N (𝒪 R)) U s φ)).app
          (op (Over.mk (𝟙 U.unop)))) (scalarExtensionSection α N U t x) =
      s * t * α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) := by
  rw [scalarExtensionDualMap, scalarExtensionLift_tmul]
  change S.obj.map (𝟙 U.unop).op s *
    (show S.obj.obj U from (scalarDualBaseSection α N U φ).app
      (op (Over.mk (𝟙 U.unop))) (scalarExtensionSection α N U t x)) = _
  erw [scalarDualBaseSection_tmul]
  change S.obj.map (𝟙 U) s *
    (α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * t) = _
  erw [S.obj.map_id]
  change s * (α.hom.app U (φ.app (op (Over.mk (𝟙 U.unop))) x) * t) = _
  ac_rfl

/-- scalarExtensionDual_hom_ext: the scalar-extension evaluation construction.
Source: Stacks Project, Tags 03EK and 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation).
The balanced section formula descends through the locally bijective sheafification
unit on each slice. Equality on pure tensors proves linearity and naturality. -/
theorem scalarExtensionDual_hom_ext
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S)
    (L : SheafOfModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (N : Mod R)
    (f g : changeOfRingsOfUniverses α L ⟶
      homObj (changeOfRingsOfUniverses α N) (𝒪 S))
    (h : ∀ (U : Cᵒᵖ) (s t : S.obj.obj U) (φ : L.val.obj U) (x : N.val.obj U),
      (f.val.app U (scalarExtensionSection α L U s φ)).app
          (op (Over.mk (𝟙 U.unop))) (scalarExtensionSection α N U t x) =
        (g.val.app U (scalarExtensionSection α L U s φ)).app
          (op (Over.mk (𝟙 U.unop))) (scalarExtensionSection α N U t x)) : f = g := by
  apply scalarExtension_hom_ext α L
  intro U s φ
  apply scalarDual_section_ext α N U
  intro W t x
  have hf := PresheafOfModules.naturality_apply f.val W.unop.hom.op
    (scalarExtensionSection α L U s φ)
  have hg := PresheafOfModules.naturality_apply g.val W.unop.hom.op
    (scalarExtensionSection α L U s φ)
  have hh := h (op W.unop.left) (S.obj.map W.unop.hom.op s) t
    (L.val.map W.unop.hom.op φ) x
  rw [← scalarExtensionSection_naturality α L] at hh
  rw [hf, hg] at hh
  change (f.val.app U (scalarExtensionSection α L U s φ)).app
      (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))
      (scalarExtensionSection α N (op W.unop.left) t x) =
    (g.val.app U (scalarExtensionSection α L U s φ)).app
      (op (Over.mk (𝟙 W.unop.left ≫ W.unop.hom)))
      (scalarExtensionSection α N (op W.unop.left) t x) at hh
  exact (PresheafOfModules.restrictOver_hom_app_congr
    (f.val.app U (scalarExtensionSection α L U s φ))
    (Category.id_comp W.unop.hom) _).symm.trans
      (hh.trans (PresheafOfModules.restrictOver_hom_app_congr
        (g.val.app U (scalarExtensionSection α L U s φ))
        (Category.id_comp W.unop.hom) _))

/-- The dual comparison evaluates by its balanced formula on every slice.
Source: Stacks Project, Tag 04TT
(blueprint: lem-sp-scalar-extension-dual-evaluation). -/
theorem scalarExtensionDualMap_tmul_slice
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
    [HasWeakSheafify J AddCommGrpCat.{max uC vC u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (α : R ⟶ S) (N : Mod R)
    (U : Cᵒᵖ) (s : S.obj.obj U) (φ : (homObj N (𝒪 R)).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (t : S.obj.obj (op W.unop.left))
    (x : N.val.obj (op W.unop.left)) :
    (((scalarExtensionDualMap α N).val.app U
        (scalarExtensionSection α (homObj N (𝒪 R)) U s φ)).app W)
          (scalarExtensionSection α N (op W.unop.left) t x) =
      S.obj.map W.unop.hom.op s * t *
        α.hom.app (op W.unop.left) (φ.app W x) := by
  rw [scalarExtensionDualMap, scalarExtensionLift_tmul]
  change S.obj.map W.unop.hom.op s *
    (show S.obj.obj (op W.unop.left) from
      (scalarDualBaseSection α N U φ).app W
        (scalarExtensionSection α N (op W.unop.left) t x)) = _
  rw [scalarDualBaseSection_tmul]
  dsimp only [Functor.comp_obj, Functor.op_obj] at *
  change S.obj.map W.unop.hom.op s *
      (α.hom.app (op W.unop.left) (φ.app W x) * t) = _
  ac_rfl

end SheafOfModules
