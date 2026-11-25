/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.RingedProjectionRestrictionData
public import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Localized module adjunction for independent site universes

Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(auxiliary; not a blueprint node).
The construction retains the actual direct-sum presheaf and its sheafification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : C)

/-- Actual direct-sum extension followed by sheafification, at independent site universes.
Source: Stacks 03DI (auxiliary; not a blueprint node). -/
abbrev localizedSystemExtension :
    SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U) ⥤
    SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) :=
  extensionByZeroPresheaf.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U ⋙
      PresheafOfModules.sheafification (𝟙 _)

/-- Actual restriction to the slice, retaining the same section modules and maps.
Source: Stacks 03DJ (auxiliary; not a blueprint node). -/
abbrev localizedSystemRestriction :
    SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) ⥤
    SheafOfModules.{max c v r}
      (((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U) :=
  overFunctor.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U

open Classical in
private theorem extensionRestrict_of
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) :
    F ⟶ (overFunctor R U).obj G where
  val.app X := ModuleCat.ofHom
    ((a.app (Opposite.op X.unop.left)).hom.comp
      (DirectSum.lof (R.obj.obj (Opposite.op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom))
  val.naturality {X Y} f := by
    ext x
    have h := PresheafOfModules.naturality_apply a
      ((Over.forget U).op.map f)
      (DirectSum.of _ X.unop.hom x)
    change a.app (Opposite.op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd R U F ((Over.forget U).op.map f)
          (DirectSum.of _ X.unop.hom x)) = _ at h
    have hr := extensionRestrict_of.{c, v, r} R U F ((Over.forget U).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    erw [hr] at h
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at h
    change a.app (Opposite.op Y.unop.left)
        (DirectSum.of (fun φ : Y.unop.left ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk φ))) Y.unop.hom (F.val.map f x)) =
      G.val.map ((Over.forget U).op.map f)
        (a.app (Opposite.op X.unop.left)
          (DirectSum.of (fun φ : X.unop.left ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom x))
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
    (a : F ⟶ (overFunctor R U).obj G) :
    extensionByZeroPresheafObj R U F ⟶ G.val where
  app V := ModuleCat.ofHom (DirectSum.toModule _ _ _
    (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
  naturality {V W} f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      change (DirectSum.toModule (R.obj.obj W) _ (G.val.obj W)
        (fun ψ : W.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (extensionByZeroPresheafRestrictAdd R U F f
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x)) =
          G.val.map f ((DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x))
      erw [extensionRestrict_of.{c, v, r} R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor R U).obj G) where
  toFun := extensionPresheafToHom.{c, v, r} R U F G
  invFun := extensionHomToPresheaf.{c, v, r} R U F G
  left_inv a := by
    ext V x
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.app V).hom.comp
        (DirectSum.lof (R.obj.obj V) _ _ φ))) x = (a.app V) x
    exact (DirectSum.toModule.unique _ (a.app V).hom x).symm
  right_inv a := by
    ext X x
    change (DirectSum.toModule (R.obj.obj (Opposite.op X.unop.left)) _
      (G.val.obj (Opposite.op X.unop.left))
      (fun φ : X.unop.left ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
        (DirectSum.lof _ _ _ X.unop.hom x) = (a.val.app X) x
    erw [DirectSum.toModule_lof]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F : SheafOfModules.{max c v r} (R.over U)) (G H : SheafOfModules.{max c v r} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv.{c, v, r} R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv.{c, v, r} R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max c v r}) (U : C)
    (F H : SheafOfModules.{max c v r} (R.over U)) (G : SheafOfModules.{max c v r} R)
    (a : H ⟶ F) (b : F ⟶ (overFunctor R U).obj G) :
    (extensionPresheafHomEquiv.{c, v, r} R U H G).symm (a ≫ b) =
      (extensionByZeroPresheaf R U).map a ≫
        (extensionPresheafHomEquiv.{c, v, r} R U F G).symm b := by
  ext V x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun ψ : V.unop ⟶ U ↦ ((a ≫ b).val.app (Opposite.op (Over.mk ψ))).hom))
        (DirectSum.of _ φ x) =
      (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
        (fun ψ : V.unop ⟶ U ↦ (b.val.app (Opposite.op (Over.mk ψ))).hom))
          (DirectSum.lmap (R := R.obj.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom)
              (DirectSum.of _ φ x))
    erw [DirectSum.lmap_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafAdjunction
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J RingCat.{max c v r}) (U : C) :
    (extensionByZeroPresheaf.{max c v r} R U ⋙
      PresheafOfModules.sheafification.{max c v r} (𝟙 R.obj)) ⊣ overFunctor.{max c v r} R U := by
  refine Adjunction.mkOfHomEquiv ?_
  refine
    { homEquiv := fun F G ↦
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
          (extensionPresheafHomEquiv.{c, v, r} R U F G)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro H F G a b
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((extensionPresheafHomEquiv.{c, v, r} R U H G).symm (a ≫ b)) = _
    rw [extensionPresheafHomEquiv_naturality_left_symm.{c, v, r}]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv.{c, v, r} R U F G).symm b)
    have heq (P : PresheafOfModules.{max c v r} R.obj) (G : SheafOfModules.{max c v r} R) :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P G =
          PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [heq, heq] at h
    exact h
  · intro F G H a b
    change extensionPresheafHomEquiv.{c, v, r} R U F H
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b)) = _
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right
      a b
    change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) a ≫ b.val at h
    erw [h]
    exact extensionPresheafHomEquiv_naturality_right.{c, v, r} R U F G H _ b

/-- Exactness of both actual localized module functors.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node).
Proof: the direct-sum Hom correspondence followed by module sheafification gives the
extension/restriction adjunction. Restriction is additive componentwise, and its left
adjoint is additive. Extension preserves colimits by adjunction and monomorphisms by
sectionwise injectivity of direct sums and left exactness of module sheafification.
The abelian exactness criteria then give its finite-limit preservation. Restriction
preserves limits by adjunction. Its composite with the module forgetful functor is
abelian-sheaf restriction, which preserves colimits by the cocontinuous site adjunction.
Reflect finite colimits through the faithful exact module forgetful functor.
All constructions remain in max c v r; no equality of the site universes is imposed. -/
theorem localizedSystemExact :
    (localizedSystemExtension.{c, v, r} R U).Additive ∧
    PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) ∧
    PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) ∧
    (localizedSystemRestriction.{c, v, r} R U).Additive ∧
    PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) ∧
    PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) := by
  let S := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
  let L := localizedSystemExtension.{c, v, r} R U
  let T := localizedSystemRestriction.{c, v, r} R U
  let : PreservesFilteredColimitsOfSize.{max c v, max c v}
      (CategoryTheory.forget AddCommGrpCat.{max c v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max c v, max c v r,
      max c v, max c v r} _
  have : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
      max c v r, max c v r + 1, v, max c v, max c v r} _ _
  have : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  let adj : L ⊣ T := extensionSheafAdjunction.{c, v, r} S U
  have : PreservesColimitsOfSize.{0, 0} L :=
    adj.leftAdjoint_preservesColimits
  have : T.Additive := by
    constructor
    intro X Y f g
    ext V x
    rfl
  have : L.Additive := adj.left_adjoint_additive
  have : (extensionByZeroPresheaf.{max c v r} S U).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    apply PresheafOfModules.mono_of_injective
    intro V
    change Function.Injective (DirectSum.lmap (R := S.obj.obj V)
      (fun φ : V.unop ⟶ U ↦ (f.val.app (op (Over.mk φ))).hom))
    apply (DirectSum.lmap_injective _).mpr
    intro φ
    apply (ModuleCat.mono_iff_injective _).mp
    exact inferInstanceAs (Mono ((evaluation.{max c v r} (S.over U) (op (Over.mk φ))).map f))
  have : L.PreservesMonomorphisms :=
    inferInstanceAs ((extensionByZeroPresheaf.{max c v r} S U ⋙
      PresheafOfModules.sheafification.{max c v r} (𝟙 S.obj)).PreservesMonomorphisms)
  have : L.PreservesHomology := L.preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesFiniteLimits L := L.preservesFiniteLimits_of_preservesHomology
  have : PreservesLimitsOfSize.{0, 0} T := adj.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{0, 0}
      (J.overPullback AddCommGrpCat.{max c v r} U) :=
    ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{max c v r}
      (J.over U) J).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (toSheaf.{max c v r} S) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteColimits (T ⋙ toSheaf.{max c v r} (S.over U)) :=
    inferInstanceAs (PreservesFiniteColimits
      (toSheaf.{max c v r} S ⋙ J.overPullback AddCommGrpCat.{max c v r} U))
  have : PreservesFiniteColimits (toSheaf.{max c v r} (S.over U)) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful (S.over U)).2.2.1
  have : ReflectsFiniteColimits (toSheaf.{max c v r} (S.over U)) :=
    inferInstance
  have : PreservesFiniteColimits T :=
    preservesFiniteColimits_of_reflects_of_preserves T (toSheaf.{max c v r} (S.over U))
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemExtensionAdditive : (localizedSystemExtension.{c, v, r} R U).Additive :=
  (localizedSystemExact.{c, v, r} R U).1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemExtensionLimits :
    PreservesFiniteLimits (localizedSystemExtension.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemExtensionColimits :
    PreservesFiniteColimits (localizedSystemExtension.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemRestrictionAdditive : (localizedSystemRestriction.{c, v, r} R U).Additive :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemRestrictionLimits :
    PreservesFiniteLimits (localizedSystemRestriction.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.2.1

/-- Exactness component for the actual localized functor.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
instance localizedSystemRestrictionColimits :
    PreservesFiniteColimits (localizedSystemRestriction.{c, v, r} R U) :=
  (localizedSystemExact.{c, v, r} R U).2.2.2.2.2

open Classical in
/-- The normalized localized adjunction, uniquely fixed by the summand injection unit.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node).
Proof: direct-sum elimination sends a map from the extension to a compatible map on each
slice object. Its inverse includes each section in the summand of its structure arrow.
Sheafification extends this natural bijection uniquely to sheaves. The summands generate
locally, so the displayed unit determines the adjunction uniquely. -/
theorem localizedSystemAdjunction_existsUnique :
    ∃! adj : localizedSystemExtension.{c, v, r} R U ⊣
      localizedSystemRestriction.{c, v, r} R U,
      ∀ (M : SheafOfModules.{max c v r}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U))
        (W : (Over U)ᵒᵖ) (x : M.val.obj W),
        (adj.unit.app M).val.app W x =
          ((PresheafOfModules.sheafificationAdjunction.{max c v r, v, max c v r, c}
            (𝟙 ((sheafCompose J
              (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).unit.app
                ((extensionByZeroPresheaf.{max c v r}
                  ((sheafCompose J
                    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U).obj M)).app
            (op W.unop.left)
              (DirectSum.lof (R.obj.obj (op W.unop.left)) (W.unop.left ⟶ U)
                (fun a ↦ M.val.obj (op (Over.mk a))) W.unop.hom x) := by
  let S := (sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R
  let adj := extensionSheafAdjunction.{c, v, r} S U
  refine ⟨adj, ?_, ?_⟩
  · intro M W x
    rfl
  · intro adj' h'
    apply Adjunction.ext
    ext M W x
    exact h' M W x

/-- The actual adjunction selected by the unique prescribed unit.
Source: Stacks 03DI--03DJ
(auxiliary; not a blueprint node). -/
def localizedSystemAdjunction : localizedSystemExtension.{c, v, r} R U ⊣
    localizedSystemRestriction.{c, v, r} R U :=
  (localizedSystemAdjunction_existsUnique.{c, v, r} R U).exists.choose

end SheafOfModules
