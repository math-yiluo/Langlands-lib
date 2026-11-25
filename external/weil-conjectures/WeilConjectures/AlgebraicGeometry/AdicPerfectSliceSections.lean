/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Constant module adjunction on a slice and the unit identity for mates

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.AdicQuotientSections

attribute [local irreducible] derivedExtension extend change
attribute [local instance 30000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

section Constant
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)
  (A : Type w) [CommRing A] (U : C)

/-- The coefficient unit restricted to the slice. Source: Stacks 03CY
(auxiliary; not a blueprint node). -/
def localRingUnit :
    (Functor.const (Over U)ᵒᵖ).obj (RingCat.of A) ⟶
      (siteModuleRings ((constant T A).over U)).obj :=
  whiskerLeft (Over.forget U).op (realizationRingUnit T A)

instance localRingUnit_injective :
    Presheaf.IsLocallyInjective (T.over U) (localRingUnit T A U) := by
  have := (realizationRingUnit_locallyBijective T A).1
  change Presheaf.IsLocallyInjective (T.over U) (whiskerLeft _ _)
  exact Presheaf.isLocallyInjective_whisker (T.over U) T (Over.forget U) _

instance localRingUnit_surjective :
    Presheaf.IsLocallySurjective (T.over U) (localRingUnit T A U) := by
  have := (realizationRingUnit_locallyBijective T A).2
  change Presheaf.IsLocallySurjective (T.over U) (whiskerLeft _ _)
  exact Presheaf.isLocallySurjective_whisker (T.over U) T (Over.forget U) _

/-- Constant module sheafification directly on the slice. Source: Stacks 03CY
(auxiliary; not a blueprint node). -/
def localConstant : ModuleCat.{w} A ⥤ Mod ((constant T A).over U) :=
  siteConstantModulePresheafGeneral (C := Over U) A ⋙
    PresheafOfModules.sheafification (localRingUnit T A U)

/-- Terminal sections with their original algebraic scalars. Source: Stacks 03CY
(auxiliary; not a blueprint node). -/
def localSections : Mod ((constant T A).over U) ⥤ ModuleCat.{w} A :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.restrictScalars (localRingUnit T A U) ⋙
      PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))

/-- Constant module presheaves are left adjoint to evaluation at the terminal object.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def constantPresheafAdjunction {D : Type w} [SmallCategory D]
    (V : D) (hV : IsTerminal V) :
    siteConstantModulePresheafGeneral (C := D) A ⊣
      PresheafOfModules.evaluation ((Functor.const Dᵒᵖ).obj (RingCat.of A)) (op V) where
  unit := { app := fun _ ↦ 𝟙 _ }
  counit :=
    { app := fun P ↦
        { app := fun W ↦ P.map (hV.from W.unop).op
          naturality := by
            intro W Z f
            ext x
            change P.map (hV.from Z.unop).op x =
              P.map f (P.map (hV.from W.unop).op x)
            have h : (hV.from W.unop).op ≫ f = (hV.from Z.unop).op := by
              change (hV.from W.unop).op ≫ f.unop.op = _
              rw [← op_comp]
              exact congrArg Quiver.Hom.op (hV.hom_ext _ _)
            rw [← PresheafOfModules.map_comp_apply, h] }
      naturality := by
        intro P Q f
        ext W x
        exact (PresheafOfModules.naturality_apply f (hV.from W.unop).op x).symm }
  left_triangle_components M := by
    ext W x
    rfl
  right_triangle_components P := by
    ext x
    change P.map (hV.from V).op x = x
    have h : hV.from V = 𝟙 V := hV.hom_ext _ _
    rw [h]
    exact congrArg (fun f ↦ f x) (P.map_id (op V))

/-- Constant realization on the slice is left adjoint to algebraic sections.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def localAdjunction : localConstant T A U ⊣ localSections T A U :=
  (constantPresheafAdjunction A (Over.mk (𝟙 U)) (Over.mkIdTerminal (X := U))).comp
    (PresheafOfModules.sheafificationAdjunction (localRingUnit T A U))

/-- Restrict the module sheafification unit, then extend by sheafification on the slice.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def localConstantMap (M : ModuleCat.{w} A) :
    (localConstant T A U).obj M ⟶
      ((commutativeSiteConstantModuleFunctor T A).obj M).over U := by
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  exact (PresheafOfModules.sheafificationHomEquiv (localRingUnit T A U)).symm
    { app := fun V ↦
        ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit T A)).unit.app
          ((siteConstantModulePresheafGeneral (C := C) A).obj M)).app
            (op V.unop.left)
      naturality := by
        intro V W f
        exact (((PresheafOfModules.sheafificationAdjunction
          (realizationRingUnit T A)).unit.app
            ((siteConstantModulePresheafGeneral (C := C) A).obj M)).naturality
              f.unop.left.op) }

/-- The comparison preserves the original constant generators.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem localConstantMap_fac (M : ModuleCat.{w} A) :
    toSheafify (T.over U)
        ((siteConstantModulePresheafGeneral (C := Over U) A).obj M).presheaf ≫
      (PresheafOfModules.toPresheaf _).map (localConstantMap T A U M).val =
        whiskerLeft (Over.forget U).op
          (toSheafify T ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf) := by
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  unfold localConstantMap
  rw [← PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  exact congrArg (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationHomEquiv (localRingUnit T A U)).apply_symm_apply _)

/-- Restriction to a slice preserves the locally bijective sheafification unit.
Source: Stacks 00XR, 03CY (auxiliary; not a blueprint node). -/
theorem localConstantMap_isIso (M : ModuleCat.{w} A) :
    IsIso (localConstantMap T A U M) := by
  have hi : Presheaf.IsLocallyInjective (T.over U)
      (whiskerLeft (Over.forget U).op
        (toSheafify T ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf)) :=
    Presheaf.isLocallyInjective_whisker (T.over U) T (Over.forget U) _
  have hs : Presheaf.IsLocallySurjective (T.over U)
      (whiskerLeft (Over.forget U).op
        (toSheafify T ((siteConstantModulePresheafGeneral (C := C) A).obj M).presheaf)) :=
    Presheaf.isLocallySurjective_whisker (T.over U) T (Over.forget U) _
  let a := toSheafify (T.over U)
    ((siteConstantModulePresheafGeneral (C := Over U) A).obj M).presheaf
  let b := (PresheafOfModules.toPresheaf _).map (localConstantMap T A U M).val
  have hi' : Presheaf.IsLocallyInjective (T.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (T.over U) a b]
    rw [localConstantMap_fac]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (T.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (T.over U) a b]
    rw [localConstantMap_fac]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi', hs'⟩

/-- The comparison between constant module sheafifications on the two sites.
Source: Stacks 00XR, 03CY (auxiliary; not a blueprint node). -/
def localConstantIso : localConstant T A U ≅
    commutativeSiteConstantModuleFunctor T A ⋙ SheafOfModules.overFunctor _ U := by
  have hIso (M : ModuleCat.{w} A) : IsIso (localConstantMap T A U M) :=
    localConstantMap_isIso T A U M
  refine NatIso.ofComponents (fun M ↦ asIso (localConstantMap T A U M)) ?_
  intro M N f
  change (localConstant T A U).map f ≫ localConstantMap T A U N =
    localConstantMap T A U M ≫
      (commutativeSiteConstantModuleFunctor T A ⋙ SheafOfModules.overFunctor _ U).map f
  have := (realizationRingUnit_locallyBijective T A).1
  have := (realizationRingUnit_locallyBijective T A).2
  let a := PresheafOfModules.sheafificationAdjunction (localRingUnit T A U)
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
      ((PresheafOfModules.sheafification (localRingUnit T A U)).map
        ((siteConstantModulePresheafGeneral (C := Over U) A).map f) ≫ _) = _
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
  simp only [a, localConstantMap,
    PresheafOfModules.sheafificationAdjunction_homEquiv_apply, Equiv.apply_symm_apply]
  ext V x
  exact congrArg (fun t ↦ t.app (op V.unop.left) x)
    ((PresheafOfModules.sheafificationAdjunction (realizationRingUnit T A)).unit.naturality
      ((siteConstantModulePresheafGeneral (C := C) A).map f))

/-- Scalar extension commutes with restriction to the slice.
Source: Stacks 03EK, 00XR (auxiliary; not a blueprint node). -/
theorem changeOverIso_exists {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    Nonempty (SheafOfModules.overFunctor _ U ⋙
        change ((T.overPullback CommRingCat U).map f) ≅
      change f ⋙ SheafOfModules.overFunctor _ U) :=
  ⟨NatIso.ofComponents (AdicPerfectModel.changeOverIso f U)
    (fun g ↦ AdicPerfectModel.changeOverIso_naturality f U g)⟩

/-- The proved scalar/restriction comparison. Source: Stacks 03EK, 00XR
(auxiliary; not a blueprint node). -/
def changeOverIso {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    SheafOfModules.overFunctor _ U ⋙ change ((T.overPullback CommRingCat U).map f) ≅
      change f ⋙ SheafOfModules.overFunctor _ U :=
  Classical.choice (changeOverIso_exists T U f)

/-- Fixed-scalar presheaf underlying a module on the slice.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def fixedPresheaf (M : Mod ((constant T A).over U)) :
    (Over U)ᵒᵖ ⥤ ModuleCat.{w} A :=
  let P := (PresheafOfModules.restrictScalars (localRingUnit T A U)).obj M.val
  { obj := P.obj
    map := fun f ↦ P.map f
    map_id := fun V ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id V)
    map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x }

/-- Forget the sheafified scalar action, retaining all algebraic scalars.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def fixedScalars : Mod ((constant T A).over U) ⥤ Sheaf (T.over U) (ModuleCat.{w} A) where
  obj M := ⟨fixedPresheaf T A U M,
    Presheaf.isSheaf_of_isSheaf_comp (T.over U) _
      (forget₂ (ModuleCat.{w} A) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom :=
    { app := fun V ↦ (ModuleCat.restrictScalars ((localRingUnit T A U).app V).hom).map
        (f.val.app V)
      naturality := by
        intro V W g
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

/-- The constant generators considered with their algebraic scalar action.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def fixedConstantUnit (M : ModuleCat.{w} A) :
    (Functor.const (Over U)ᵒᵖ).obj M ⟶
      ((fixedScalars T A U).obj ((localConstant T A U).obj M)).obj where
  app V := ((PresheafOfModules.sheafificationAdjunction (localRingUnit T A U)).unit.app
    ((siteConstantModulePresheafGeneral (C := Over U) A).obj M)).app V
  naturality := by
    intro V W g
    exact (((PresheafOfModules.sheafificationAdjunction (localRingUnit T A U)).unit.app
      ((siteConstantModulePresheafGeneral (C := Over U) A).obj M)).naturality g)

instance fixedConstantUnit_injective (M : ModuleCat.{w} A) :
    Presheaf.IsLocallyInjective (T.over U) (fixedConstantUnit T A U M) where
  equalizerSieve_mem x y h := Presheaf.equalizerSieve_mem (T.over U)
    (toSheafify (T.over U)
      ((siteConstantModulePresheafGeneral (C := Over U) A).obj M).presheaf) x y h

instance fixedConstantUnit_surjective (M : ModuleCat.{w} A) :
    Presheaf.IsLocallySurjective (T.over U) (fixedConstantUnit T A U M) where
  imageSieve_mem x := Presheaf.imageSieve_mem (T.over U)
    (toSheafify (T.over U)
      ((siteConstantModulePresheafGeneral (C := Over U) A).obj M).presheaf) x

/-- Sheafify the algebraic constant generators.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def fixedConstantMap (M : ModuleCat.{w} A) :
    (constantSheaf (T.over U) (ModuleCat.{w} A)).obj M ⟶
      (fixedScalars T A U).obj ((localConstant T A U).obj M) :=
  ((sheafificationAdjunction (T.over U) (ModuleCat.{w} A)).homEquiv _ _).symm
    (fixedConstantUnit T A U M)

/-- Both module and fixed-scalar sheafifications have the same locally bijective unit.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
theorem fixedConstantMap_isIso (M : ModuleCat.{w} A) :
    IsIso (fixedConstantMap T A U M) := by
  let a := toSheafify (T.over U) ((Functor.const (Over U)ᵒᵖ).obj M)
  let b := (fixedConstantMap T A U M).hom
  have h : a ≫ b = fixedConstantUnit T A U M :=
    ((sheafificationAdjunction (T.over U) (ModuleCat.{w} A)).homEquiv _ _).apply_symm_apply _
  have hi : Presheaf.IsLocallyInjective (T.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (T.over U) a b, h]
    infer_instance
  have hs : Presheaf.IsLocallySurjective (T.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (T.over U) a b, h]
    infer_instance
  exact (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hi, hs⟩

/-- Fixed scalars identify module constant realization with the fixed-module constant sheaf.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def fixedConstantIso : constantSheaf (T.over U) (ModuleCat.{w} A) ≅
    localConstant T A U ⋙ fixedScalars T A U := by
  have hIso (M : ModuleCat.{w} A) : IsIso (fixedConstantMap T A U M) :=
    fixedConstantMap_isIso T A U M
  refine NatIso.ofComponents (fun M ↦ asIso (fixedConstantMap T A U M)) ?_
  intro M N f
  change (constantSheaf (T.over U) (ModuleCat.{w} A)).map f ≫
      fixedConstantMap T A U N =
    fixedConstantMap T A U M ≫ (localConstant T A U ⋙ fixedScalars T A U).map f
  let a := sheafificationAdjunction (T.over U) (ModuleCat.{w} A)
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _
      ((presheafToSheaf (T.over U) (ModuleCat.{w} A)).map
        ((Functor.const (Over U)ᵒᵖ).map f) ≫ _) = _
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right]
  simp only [a, fixedConstantMap, Equiv.apply_symm_apply]
  ext V x
  exact congrArg (fun t ↦ t.app V x)
    ((PresheafOfModules.sheafificationAdjunction (localRingUnit T A U)).unit.naturality
      ((siteConstantModulePresheafGeneral (C := Over U) A).map f))

/-- The constant-module/sections monad is the usual constant fixed-module section functor.
Source: Stacks 03CY (auxiliary; not a blueprint node). -/
def sectionsIso : AdicCohomology.sections (R := A) (T.over U) (Over.mk (𝟙 U)) ≅
    localConstant T A U ⋙ localSections T A U :=
  Functor.isoWhiskerRight (fixedConstantIso T A U)
    ((sheafSections (T.over U) (ModuleCat.{w} A)).obj (op (Over.mk (𝟙 U))))

end Constant

section Mates
set_option backward.defeqAttrib.useBackward true
variable {B D E : Type*} [Category* B] [Category* D] [Category* E]
  {F₀ : B ⥤ D} {R₀ : D ⥤ B} {F₁ : B ⥤ E} {R₁ : E ⥤ B} {C₀ : E ⥤ D}
  (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (θ : F₁ ⋙ C₀ ≅ F₀)

/-- The mate of inverse balancing. Source: adjunction unit/counit identities
(auxiliary; not a blueprint node). -/
def balancingMate : R₁ ⟶ C₀ ⋙ R₀ where
  app N := a₀.unit.app (R₁.obj N) ≫
    R₀.map (θ.inv.app (R₁.obj N) ≫ C₀.map (a₁.counit.app N))
  naturality {M N} f := by
    change R₁.map f ≫ (a₀.unit.app (R₁.obj N) ≫ _) =
      (a₀.unit.app (R₁.obj M) ≫ _) ≫ R₀.map (C₀.map f)
    rw [← a₀.unit_naturality_assoc]
    simp only [← R₀.map_comp, Category.assoc]
    congr 2
    rw [θ.inv.naturality_assoc]
    simp only [Functor.comp_map, ← C₀.map_comp]
    rw [a₁.counit_naturality]

/-- A balancing mate intertwines the units. Source: adjunction unit/counit identities
(auxiliary; not a blueprint node). -/
theorem balancingMate_unit (M : B) :
    a₀.unit.app M = a₁.unit.app M ≫
      (balancingMate a₀ a₁ θ).app (F₁.obj M) ≫ R₀.map (θ.hom.app M) := by
  let i : M ⟶ R₁.obj (F₁.obj M) := a₁.unit.app M
  have hi : F₁.map i ≫ a₁.counit.app (F₁.obj M) = 𝟙 _ :=
    a₁.left_triangle_components M
  have h : F₀.map i ≫
      θ.inv.app (R₁.obj (F₁.obj M)) ≫ C₀.map (a₁.counit.app (F₁.obj M)) ≫
      θ.hom.app M = 𝟙 _ := by
    rw [θ.inv.naturality_assoc i]
    simp only [Functor.comp_map]
    rw [← C₀.map_comp_assoc, hi, C₀.map_id, Category.id_comp, θ.inv_hom_id_app]
  change a₀.unit.app M = i ≫
    (a₀.unit.app (R₁.obj (F₁.obj M)) ≫ R₀.map _) ≫ R₀.map (θ.hom.app M)
  rw [Category.assoc, ← a₀.unit_naturality_assoc i]
  simp only [← R₀.map_comp, Category.assoc]
  rw [h, R₀.map_id, Category.comp_id]

end Mates

end AlgebraicGeometry.Scheme.AdicQuotientSections
