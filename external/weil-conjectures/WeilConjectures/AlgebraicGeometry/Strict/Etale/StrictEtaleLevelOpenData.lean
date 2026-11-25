/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.StrictEtaleOpenScalarMate.StrictEtaleFixedScalarOpenMate
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! Levelwise data for strict étale extension by zero.

This isolates the fixed coefficient-level transport from the subsequent system assembly.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

namespace StrictEtaleOpenProof

open Opposite CategoryTheory.MonoidalCategory
open scoped CategoryTheory.TwoSquare

private abbrev coefficient (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ) :=
  O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)

private abbrev ring (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))

private def unit (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (Functor.const T.Etaleᵒᵖ).obj (RingCat.of A) ⟶ (ring T A).obj :=
  whiskerRight (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private def fixed (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.{u + 1} (ring T A) ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) where
  obj M :=
    let P := (PresheafOfModules.restrictScalars (unit T A)).obj M.val
    ⟨{ obj := P.obj
       map := fun f ↦ P.map f
       map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (P.map_id U) x
       map_comp := fun f g ↦ by ext x; exact P.map_comp_apply f g x },
      Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map f := ⟨{
    app := fun U ↦ (ModuleCat.restrictScalars ((unit T A).app U).hom).map (f.val.app U)
    naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }⟩

private instance fixedAdditive (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixed T A).Additive where
  map_add := by intros; ext U x; rfl

private instance ringForgetSheafification (T : Scheme.{u}) :
    T.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  le := by
    intro P Q f hf
    let : Presheaf.IsLocallyInjective T.smallEtaleTopology f := hf.isLocallyInjective
    let : Presheaf.IsLocallySurjective T.smallEtaleTopology f := hf.isLocallySurjective
    let : Presheaf.IsLocallyInjective T.smallEtaleTopology (Functor.whiskerRight f
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem T.smallEtaleTopology f x y h⟩
    let : Presheaf.IsLocallySurjective T.smallEtaleTopology (Functor.whiskerRight f
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem T.smallEtaleTopology f x⟩
    exact T.smallEtaleTopology.W_of_isLocallyBijective (Functor.whiskerRight f
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))

private def ringIso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    ring T A ≅ (constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of A) :=
  (constantCommuteCompose T.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of A)

private theorem ringIso_unit (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    unit T A ≫ (ringIso T A).hom.hom =
      toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A)) := by
  change unit T A ≫
    ((constantCommuteCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  unfold unit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality T.smallEtaleTopology
    (Functor.constComp T.Etaleᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom).symm.trans (by rfl)

private def standardFixed (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.{u + 1} (ring T A) ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  SheafOfModules.restrictScalars (ringIso T A).inv ⋙
    constantRingModuleRestriction T.smallEtaleTopology A

private def restrictCancelIso (T : Scheme.{u}) {R S : Sheaf T.smallEtaleTopology RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : T.Etaleᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private instance standardFixedEquivalence (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (standardFixed T A).IsEquivalence := by
  obtain ⟨e, he, _, _, _⟩ := (constant_ring_module_sheaves T.smallEtaleTopology A).1
  have : (constantRingModuleRestriction T.smallEtaleTopology A).IsEquivalence :=
    he ▸ e.isEquivalence_functor
  let c := ringIso T A
  let e' := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars.{u + 1} c.inv)
    (SheafOfModules.restrictScalars.{u + 1} c.hom)
    (restrictCancelIso T c.hom c.inv c.hom_inv_id).symm
    (restrictCancelIso T c.inv c.hom c.inv_hom_id)
  have : (SheafOfModules.restrictScalars.{u + 1} c.inv).IsEquivalence :=
    e'.isEquivalence_functor
  exact inferInstanceAs
    (SheafOfModules.restrictScalars c.inv ⋙
      constantRingModuleRestriction T.smallEtaleTopology A).IsEquivalence

private theorem fixed_smul (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M : SheafOfModules.{u + 1} (ring T A)) (U : T.Etaleᵒᵖ) (a : A) (x : M.val.obj U) :
    a • (show ((standardFixed T A).obj M).obj.obj U
      from x) = a • (show ((fixed T A).obj M).obj.obj U from x) := by
  have h := congrArg (fun f ↦ f.app U a) (ringIso_unit T A)
  have hi := congrArg (fun f ↦ f.hom.app U) (ringIso T A).hom_inv_id
  change (ringIso T A).inv.hom.app U
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app U a) • x =
    (unit T A).app U a • x
  erw [← h]
  exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)

private def fixedIso (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    standardFixed T A ≅ fixed T A := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      exact (fixed_smul T A M U a x).symm)
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private instance fixedEquivalence (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (fixed T A).IsEquivalence := by
  exact Functor.isEquivalence_of_iso (fixedIso T A)

private instance openMapContinuous {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).IsContinuous
      X.smallEtaleTopology Z.smallEtaleTopology :=
  Scheme.isContinuous_overMap (inferInstance : Etale j) le_rfl

private abbrev openSets {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).sheafPushforwardContinuous
    (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology

private instance etalePullbackContinuous {X Z : Scheme.{u}} (j : X ⟶ Z) :
    (MorphismProperty.Over.pullback @Etale ⊤ j).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology := by
  change (MorphismProperty.Over.pullback @Etale ⊤ j).IsContinuous
    (Z.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)
  exact Scheme.isContinuous_overPullback @Etale @Etale le_rfl j

private def setComparison {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Scheme.etaleSetPullback j ≅ openSets j :=
  (strictEtaleSetAdjunction j).leftAdjointUniq
    ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
      _root_.trivial).sheafPushforwardContinuous X.smallEtaleTopology Z.smallEtaleTopology)

private theorem setComparison_inv_naturality {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] {S T : Sheaf Z.smallEtaleTopology (Type (u + 1))}
    (f : S ⟶ T) (U : X.Etaleᵒᵖ) (x : ((openSets j).obj S).obj.obj U) :
    ((Scheme.etaleSetPullback j).map f).hom.app U
        ((setComparison j).inv.app S |>.hom.app U x) =
      ((setComparison j).inv.app T).hom.app U
        (((openSets j).map f).hom.app U x) :=
  (congrArg (fun g ↦ g.hom.app U x) ((setComparison j).inv.naturality f)).symm

private def addSections (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t : O) (n : ℕ) (M : strictEtaleLevel T O t n) :
    (coefficientUnderlying O t n).obj M ⊗ (coefficientUnderlying O t n).obj M ⟶
      (coefficientUnderlying O t n).obj M :=
  ⟨{ app := fun U ↦ ↾(fun z ↦ @Add.add (M.val.obj U) inferInstance z.1 z.2)
     naturality := by
       intro U V f
       ext z
       exact ((M.val.map f).hom.map_add _ _).symm }⟩

private theorem constantSection_apply (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t : O) (n : ℕ) (a : coefficient O t n) (U : T.Etaleᵒᵖ)
    (x : (((constantSheaf T.smallEtaleTopology (Type (u + 1))).obj
      PUnit).obj.obj U)) :
    (coefficientConstantSection (J := T.smallEtaleTopology) O t n a).hom.app U x =
      (unit T (coefficient O t n)).app U a := by
  let P := (Functor.const T.Etaleᵒᵖ).obj (PUnit : Type (u + 1))
  have hp : Presheaf.IsSheaf T.smallEtaleTopology P :=
    Presheaf.isSheaf_of_isTerminal _ Types.isTerminalPUnit
  have hi := isIso_toSheafify T.smallEtaleTopology hp
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((toSheafify T.smallEtaleTopology P).app U)).surjective x
  let R := coefficientQuotientSheaf (J := T.smallEtaleTopology) O t n
  let B := (sheafCompose T.smallEtaleTopology
    (CategoryTheory.forget CommRingCat.{u + 1})).obj R
  have he := ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).homEquiv
    P B).apply_symm_apply
      ((Functor.const T.Etaleᵒᵖ).map (TypeCat.ofHom (fun (_ : PUnit.{u + 2}) ↦ a)) ≫
        whiskerRight (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (coefficient O t n)))) (CategoryTheory.forget CommRingCat.{u + 1}))
  exact ConcreteCategory.congr_hom (congr_app he U) y

private def scalarSections (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t : O) (n : ℕ) (a : coefficient O t n) (M : strictEtaleLevel T O t n) :
    (coefficientUnderlying O t n).obj M ⟶ (coefficientUnderlying O t n).obj M :=
  ⟨{ app := fun U ↦ ↾(fun x ↦ (unit T (coefficient O t n)).app U a •
      (show M.val.obj U from x))
     naturality := by
       intro U V f
       ext x
       change (unit T (coefficient O t n)).app V a • M.val.map f x =
         M.val.map f ((unit T (coefficient O t n)).app U a •
           (show M.val.obj U from x))
       rw [M.val.map_smul]
       congr 1
       exact ConcreteCategory.congr_hom
         ((unit T (coefficient O t n)).naturality f) a }⟩

private def inverseUnderlying (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) (M : strictEtaleLevel Z O t n) :
    (openSets j).obj ((coefficientUnderlying O t n).obj M) ≅
      (coefficientUnderlying O t n).obj ((I.lift n).modules.obj M) :=
  ((setComparison j).app ((coefficientUnderlying O t n).obj M)).symm ≪≫
    ((I.lift n).moduleUnderlying.app M).symm

private theorem inverseUnderlying_add (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) (M : strictEtaleLevel Z O t n)
    (U : X.Etaleᵒᵖ)
    (x y : M.val.obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).op.obj U)) :
    (inverseUnderlying O t j I n M).hom.hom.app U (x + y) =
      (show ((I.lift n).modules.obj M).val.obj U from
        (inverseUnderlying O t j I n M).hom.hom.app U x) +
      (show ((I.lift n).modules.obj M).val.obj U from
        (inverseUnderlying O t j I n M).hom.hom.app U y) := by
  let S := (coefficientUnderlying (J := Z.smallEtaleTopology) O t n).obj M
  let z := ((setComparison j).inv.app (S ⊗ S)).hom.app U (x, y)
  have h := (I.lift n).moduleAdd M (S ⊗ S)
    (CartesianMonoidalCategory.fst S S) (CartesianMonoidalCategory.snd S S)
    (addSections Z O t n M) (fun _ _ ↦ rfl) U z
  dsimp only [z] at h
  erw [setComparison_inv_naturality, setComparison_inv_naturality,
    setComparison_inv_naturality] at h
  exact h

private theorem inverseUnderlying_smul (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) (M : strictEtaleLevel Z O t n)
    (U : X.Etaleᵒᵖ) (a : coefficient O t n)
    (x : M.val.obj ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).op.obj U)) :
    (inverseUnderlying O t j I n M).hom.hom.app U
        ((unit Z (coefficient O t n)).app
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).op.obj U) a • x) =
      (unit X (coefficient O t n)).app U a •
        (show ((I.lift n).modules.obj M).val.obj U from
          (inverseUnderlying O t j I n M).hom.hom.app U x) := by
  let L := Scheme.etaleSetPullback j
  let S := (coefficientUnderlying (J := Z.smallEtaleTopology) O t n).obj M
  let terminal : S ⟶ (constantSheaf Z.smallEtaleTopology (Type (u + 1))).obj PUnit :=
    ⟨(Functor.isTerminalConst _ Types.isTerminalPUnit).from _ ≫
      toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj PUnit)⟩
  let a' := terminal ≫ coefficientConstantSection (J := Z.smallEtaleTopology) O t n a
  let z := ((setComparison j).inv.app S).hom.app U x
  have ha : L.map a' ≫ (I.lift n).ringUnderlying.hom =
      L.map terminal ≫ I.singleton.hom ≫
        coefficientConstantSection (J := X.smallEtaleTopology) O t n a := by
    dsimp only [a']
    rw [L.map_comp, Category.assoc, I.constants]
  have h := (I.lift n).moduleSMul M S a' (𝟙 S) (scalarSections Z O t n a M) (by
    intro V y
    change (unit Z (coefficient O t n)).app V a • (show M.val.obj V from y) =
      (show (ring Z (coefficient O t n)).obj.obj V from
        (coefficientConstantSection (J := Z.smallEtaleTopology) O t n a).hom.app V
          (terminal.hom.app V y)) • (show M.val.obj V from y)
    rw [constantSection_apply]) U z
  have hc := congrArg (fun f ↦ f.hom.app U z) ha
  change (I.lift n).ringUnderlying.hom.hom.app U ((L.map a').hom.app U z) =
    (coefficientConstantSection (J := X.smallEtaleTopology) O t n a).hom.app U
      ((L.map terminal ≫ I.singleton.hom).hom.app U z) at hc
  rw [constantSection_apply] at hc
  rw [hc, L.map_id] at h
  dsimp only [z] at h
  erw [setComparison_inv_naturality] at h
  exact h

private def liftFixedMap (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (f : (sheafCompose T.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj M ⟶
      (sheafCompose T.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj N)
    (hadd : ∀ (U : T.Etaleᵒᵖ) (x y : M.obj.obj U),
      f.hom.app U (x + y) =
        (show N.obj.obj U from f.hom.app U x) + (show N.obj.obj U from f.hom.app U y))
    (hsmul : ∀ (U : T.Etaleᵒᵖ) (a : A) (x : M.obj.obj U),
      f.hom.app U (a • x) = a • (show N.obj.obj U from f.hom.app U x)) : M ⟶ N :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (X := M.obj.obj U) (Y := N.obj.obj U)
        { toFun := f.hom.app U
          map_add' := hadd U
          map_smul' := hsmul U }
     naturality := by
       intro U V g
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro x
       exact CategoryTheory.congr_fun (f.hom.naturality g) x }⟩

private def inverseComparisonInv (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) :
    fixed Z (coefficient O t n) ⋙
        Etale.openImmersionRestriction (ModuleCat.{u + 1} (coefficient O t n)) j ⟶
      (I.lift n).modules ⋙ fixed X (coefficient O t n) where
  app M := liftFixedMap X (coefficient O t n) _ _
    (inverseUnderlying O t j I n M).hom
    (inverseUnderlying_add O t j I n M) (inverseUnderlying_smul O t j I n M)
  naturality := by
    intro M N f
    ext U x
    have h₁ := setComparison_inv_naturality j ((coefficientUnderlying O t n).map f) U x
    have h₂ := congrArg (fun a ↦ a.hom.app U
      (((setComparison j).inv.app ((coefficientUnderlying O t n).obj M)).hom.app U x))
      ((I.lift n).moduleUnderlying.inv.naturality f)
    change ((I.lift n).moduleUnderlying.inv.app N).hom.app U
        (((setComparison j).inv.app ((coefficientUnderlying O t n).obj N)).hom.app U
          (f.val.app _ x)) =
      ((I.lift n).modules.map f).val.app U
        (((I.lift n).moduleUnderlying.inv.app M).hom.app U
          (((setComparison j).inv.app ((coefficientUnderlying O t n).obj M)).hom.app U x))
    exact (congrArg (fun y ↦ ((I.lift n).moduleUnderlying.inv.app N).hom.app U y)
      h₁.symm).trans h₂

private def inverseComparison (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) :
    (I.lift n).modules ⋙ fixed X (coefficient O t n) ≅
      fixed Z (coefficient O t n) ⋙
        Etale.openImmersionRestriction (ModuleCat.{u + 1} (coefficient O t n)) j := by
  let α := inverseComparisonInv O t j I n
  have hi (M : strictEtaleLevel Z O t n) : IsIso (α.app M) := by
    have hi' : IsIso ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient O t n)))).map (α.app M)) := by
      change IsIso (inverseUnderlying O t j I n M).hom
      infer_instance
    exact isIso_of_reflects_iso _
      (sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient O t n))))
  let := NatIso.isIso_of_isIso_app α
  exact (asIso α).symm

private abbrev quotientMap (O : Type (u + 1)) [CommRing O] (t : O)
    {m n : ℕ} (h : n ≤ m) : coefficient O t m →+* coefficient O t n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

set_option maxHeartbeats 800000 in
-- Compare the bundled coefficient presentations without unfolding their scalar actions.
private def fixedRestrictionMap (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t : O) {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := T.smallEtaleTopology) O t h ⋙ fixed T (coefficient O t m) ⟶
      fixed T (coefficient O t n) ⋙
        Sheaf.restrictScalars T.smallEtaleTopology (quotientMap O t h) where
  app M := liftFixedMap T (coefficient O t m) _ _
    ((coefficientRestrictionUnderlying (J := T.smallEtaleTopology) O t h).hom.app M)
    (fun _ _ _ ↦ rfl) (fun U a x ↦ by
      have hunit := ConcreteCategory.congr_hom (congr_app
        (toSheafify_naturality T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).map (CommRingCat.ofHom (quotientMap O t h)))) U) a
      exact (congrArg (fun b ↦ b • (show M.val.obj U from x)) hunit).symm)
  naturality := by
    intro M N f
    ext U x
    rfl

set_option maxHeartbeats 800000 in
-- Compare the bundled coefficient presentations without unfolding their scalar actions.
private def fixedRestriction (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (t : O) {m n : ℕ} (h : n ≤ m) :
    coefficientRestriction (J := T.smallEtaleTopology) O t h ⋙ fixed T (coefficient O t m) ≅
      fixed T (coefficient O t n) ⋙
        Sheaf.restrictScalars T.smallEtaleTopology (quotientMap O t h) := by
  let α := fixedRestrictionMap T O t h
  have hi (M : strictEtaleLevel T O t n) : IsIso (α.app M) := by
    have hi' : IsIso ((sheafCompose T.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient O t m)))).map (α.app M)) := by
      change IsIso ((coefficientRestrictionUnderlying
        (J := T.smallEtaleTopology) O t h).hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (sheafCompose T.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} (coefficient O t m))))
  let := NatIso.isIso_of_isIso_app α
  exact asIso α

private def levelFunctor (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    strictEtaleLevel X O t n ⥤ strictEtaleLevel Z O t n :=
  fixed X (coefficient O t n) ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      (fixed Z (coefficient O t n)).asEquivalence.inverse

private instance levelFunctor_additive (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    (levelFunctor O t j n).Additive := by
  let EX := (fixed X (coefficient O t n)).asEquivalence
  let EZ := (fixed Z (coefficient O t n)).asEquivalence
  have : EX.functor.Additive := fixedAdditive X (coefficient O t n)
  have : EZ.functor.Additive := fixedAdditive Z (coefficient O t n)
  change (EX.functor ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      EZ.inverse).Additive
  infer_instance

private instance levelFunctor_finiteLimits (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteLimits (levelFunctor O t j n) := by
  let EX := (fixed X (coefficient O t n)).asEquivalence
  let EZ := (fixed Z (coefficient O t n)).asEquivalence
  have : EX.functor.Additive := fixedAdditive X (coefficient O t n)
  have : EZ.functor.Additive := fixedAdditive Z (coefficient O t n)
  change PreservesFiniteLimits (EX.functor ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      EZ.inverse)
  infer_instance

private instance levelFunctor_finiteColimits (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    PreservesFiniteColimits (levelFunctor O t j n) := by
  let EX := (fixed X (coefficient O t n)).asEquivalence
  let EZ := (fixed Z (coefficient O t n)).asEquivalence
  have : EX.functor.Additive := fixedAdditive X (coefficient O t n)
  have : EZ.functor.Additive := fixedAdditive Z (coefficient O t n)
  change PreservesFiniteColimits (EX.functor ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      EZ.inverse)
  infer_instance

private def levelAdjunction (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (I : StrictEtaleOrdinaryImage O t j) (n : ℕ) :
    levelFunctor O t j n ⊣ (I.lift n).modules := by
  let EX := (fixed X (coefficient O t n)).asEquivalence
  let EZ := (fixed Z (coefficient O t n)).asEquivalence
  let a := (EX.toAdjunction.comp
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} (coefficient O t n)) j)).comp
      EZ.symm.toAdjunction
  let er : EZ.functor ⋙
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} (coefficient O t n)) j ⋙ EX.inverse) ≅
      (I.lift n).modules :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (inverseComparison O t j I n).symm EX.inverse ≪≫
        Functor.associator _ _ _ ≪≫
          isoWhiskerLeft (I.lift n).modules EX.unitIso.symm ≪≫
            Functor.rightUnitor _
  exact a.ofNatIsoRight er

universe v w

-- Transport an object comparison through the four coefficient equivalences.
private def transportObjectIso
    {A B C D A' B' C' D' : Type v}
    [Category.{w} A] [Category.{w} B] [Category.{w} C] [Category.{w} D]
    [Category.{w} A'] [Category.{w} B'] [Category.{w} C'] [Category.{w} D']
    (E : A ≌ A') (F : B ≌ B') (G : C ≌ C') (H : D ≌ D')
    (J : A' ⥤ B') (K : C' ⥤ D')
    (R : A ⥤ C) (S : B ⥤ D) (R' : A' ⥤ C') (S' : B' ⥤ D')
    (r : R ⋙ G.functor ≅ E.functor ⋙ R')
    (s : S ⋙ H.functor ≅ F.functor ⋙ S') (α : R' ⋙ K ≅ J ⋙ S') (N : A) :
    S.obj (F.inverse.obj (J.obj (E.functor.obj N))) ≅
      H.inverse.obj (K.obj (G.functor.obj (R.obj N))) :=
  H.unitIso.app _ ≪≫ H.inverse.mapIso
    (s.app _ ≪≫ S'.mapIso (F.counitIso.app _) ≪≫
      (α.app (E.functor.obj N)).symm ≪≫ K.mapIso (r.app N).symm)

-- Full faithfulness makes the unit invertible, and the object comparison handles the counit.
private theorem inverseMate_iso_of_full
    {A B C D : Type v}
    [Category.{w} A] [Category.{w} B] [Category.{w} C] [Category.{w} D]
    {J : A ⥤ B} {P : B ⥤ A} {K : C ⥤ D} {Q : D ⥤ C}
    [J.Full] [J.Faithful] [K.Full] [K.Faithful]
    {R : A ⥤ C} {S : B ⥤ D} (a : J ⊣ P) (b : K ⊣ Q)
    (β : TwoSquare P S R Q) [IsIso β]
    (e : ∀ N, S.obj (J.obj N) ≅ K.obj (R.obj N)) :
    IsIso (((mateEquiv a b).symm β)) := by
  let (N : A) : IsIso ((((mateEquiv a b).symm β)).app N) := by
    have hη : IsIso (a.unit.app N) := inferInstance
    have hβ : IsIso (β.app (J.obj N)) := inferInstance
    have hε : IsIso (b.counit.app (S.obj (J.obj N))) :=
      b.isIso_counit_app_of_iso (e N)
    simp only [mateEquiv_symm_apply, NatTrans.comp_app, id_obj, comp_obj,
      leftUnitor_inv_app, whiskerRight_app, Functor.comp_map, associator_inv_app,
      associator_hom_app, whiskerLeft_app, rightUnitor_hom_app,
      map_id, Category.id_comp, Category.comp_id]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private instance levelFunctor_full (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    (levelFunctor O t j n).Full := by
  change ((fixed X (coefficient O t n)).asEquivalence.functor ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      (fixed Z (coefficient O t n)).asEquivalence.inverse).Full
  infer_instance

private instance levelFunctor_faithful (O : Type (u + 1)) [CommRing O] (t : O)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    (levelFunctor O t j n).Faithful := by
  change ((fixed X (coefficient O t n)).asEquivalence.functor ⋙
    Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (coefficient O t n)) j ⋙
      (fixed Z (coefficient O t n)).asEquivalence.inverse).Faithful
  infer_instance

end StrictEtaleOpenProof

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (I : StrictEtaleOrdinaryImage O t j)
  (PX : StrictEtaleEvaluation X O t) (PZ : StrictEtaleEvaluation Z O t)

/-- The levelwise pieces of ordinary strict étale extension by zero.
Source: Stacks 03S2, 03DI and 03DJ; Zheng, Construction 4.1
(blueprint: new-lem-pur-strict-etale-level-open-data).

The record contains the transported lower-shriek functors, their exact adjunctions,
and the normalized scalar-restriction mates.  It is strictly below the system theorem:
it has no system extension, system adjunction, or system evaluation comparison. -/
structure StrictEtaleLevelOpenData where
  level : ∀ n, strictEtaleLevel X O t n ⥤ strictEtaleLevel Z O t n
  [levelAdditive : ∀ n, (level n).Additive]
  levelExact : ∀ n, PreservesFiniteLimits (level n) ∧ PreservesFiniteColimits (level n)
  levelAdjunction : ∀ n, level n ⊣ (I.lift n).modules
  restriction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := X.smallEtaleTopology) O t h ⋙ level m ≅
      level n ⋙ coefficientRestriction (J := Z.smallEtaleTopology) O t h
  restrictionMate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (levelAdjunction n) (levelAdjunction m)
      (.mk _ _ _ _ (restriction h).hom)) = (I.restrictInverse h).inv

attribute [instance] StrictEtaleLevelOpenData.levelAdditive

/-- The levelwise transport exists.
Source: Stacks Project 03S2, 03DI and 03DJ; Zheng, Construction 4.1.
(blueprint: new-lem-pur-strict-etale-level-open-data)

Restrict a module along the constant-presheaf sheafification unit to obtain an
additive equivalence with fixed-coefficient module sheaves. The ring comparison
`constantCommuteCompose` and `constant_ring_module_sheaves` prove this equivalence.
Transport the fixed-coefficient open extension by zero and its exact adjunction.
The addition and scalar graph equations of the supplied lift, together with its
constant-section normalization, identify its right adjoint with literal open
restriction. This gives the chosen adjunctions with `(I.lift n).modules`.

Naturality of sheafification identifies scalar restriction through the equivalences
by the identity on sections. For fixed coefficients, scalar coextension commutes
with open restriction. Taking its mate twice shows that extension by zero commutes
with scalar restriction. Transport this isomorphism through the equivalences to
identify scalar restriction of an extended object with extension of its scalar
restriction. Extension by zero and its transports are fully faithful. The inverse
mate of `I.restrictInverse.inv` is a composite of the image of the invertible unit,
the given inverse-image coefficient isomorphism, and a counit at an object
isomorphic to an extended object. That counit is invertible by full faithfulness,
so this exact inverse mate is invertible. Define `restriction` as its isomorphism;
the inverse law of `mateEquiv` gives `restrictionMate` exactly.

The constructions apply to the zero coefficient ring and to the empty open: the
same section formulas and Hom transposes give the zero functors and identities.
No nonzero-ring, regularity or completeness assumption enters the construction. -/
theorem strictEtaleLevelOpenData_exists :
    Nonempty (StrictEtaleLevelOpenData O t j I) := by
  have (n : ℕ) : (StrictEtaleOpenProof.fixed X
      (StrictEtaleOpenProof.coefficient O t n)).IsEquivalence :=
    StrictEtaleOpenProof.fixedEquivalence X (StrictEtaleOpenProof.coefficient O t n)
  have (n : ℕ) : (StrictEtaleOpenProof.fixed Z
      (StrictEtaleOpenProof.coefficient O t n)).IsEquivalence :=
    StrictEtaleOpenProof.fixedEquivalence Z (StrictEtaleOpenProof.coefficient O t n)
  let J := StrictEtaleOpenProof.levelFunctor O t j
  let a := StrictEtaleOpenProof.levelAdjunction O t j I
  have hm {m n : ℕ} (h : n ≤ m) :
      IsIso (((mateEquiv (a n) (a m)).symm
        (.mk _ _ _ _ (I.restrictInverse h).inv))) := by
    have hi := StrictEtaleOpenScalarMate.fixed_scalar_mate_iso
      (StrictEtaleOpenProof.coefficient O t m) (StrictEtaleOpenProof.coefficient O t n)
        (StrictEtaleOpenProof.quotientMap O t h) j
    let α' :
        Sheaf.restrictScalars X.smallEtaleTopology (StrictEtaleOpenProof.quotientMap O t h) ⋙
            Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t m)) j ≅
          Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t n)) j ⋙
            Sheaf.restrictScalars Z.smallEtaleTopology
              (StrictEtaleOpenProof.quotientMap O t h) := asIso (((mateEquiv
      (Etale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t n)) j)
      (Etale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t m)) j)).symm
          (.mk _ _ _ _ (𝟙 _))))
    exact StrictEtaleOpenProof.inverseMate_iso_of_full (a n) (a m)
      (.mk _ _ _ _ (I.restrictInverse h).inv)
      (StrictEtaleOpenProof.transportObjectIso
        (StrictEtaleOpenProof.fixed X (StrictEtaleOpenProof.coefficient O t n)).asEquivalence
        (StrictEtaleOpenProof.fixed Z (StrictEtaleOpenProof.coefficient O t n)).asEquivalence
        (StrictEtaleOpenProof.fixed X (StrictEtaleOpenProof.coefficient O t m)).asEquivalence
        (StrictEtaleOpenProof.fixed Z (StrictEtaleOpenProof.coefficient O t m)).asEquivalence
        (Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t n)) j)
        (Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (StrictEtaleOpenProof.coefficient O t m)) j)
        (coefficientRestriction (J := X.smallEtaleTopology) O t h)
        (coefficientRestriction (J := Z.smallEtaleTopology) O t h)
        (Sheaf.restrictScalars X.smallEtaleTopology (StrictEtaleOpenProof.quotientMap O t h))
        (Sheaf.restrictScalars Z.smallEtaleTopology (StrictEtaleOpenProof.quotientMap O t h))
        (StrictEtaleOpenProof.fixedRestriction X O t h)
        (StrictEtaleOpenProof.fixedRestriction Z O t h) α')
  let α {m n : ℕ} (h : n ≤ m) :=
    @asIso _ _ _ _ (((mateEquiv (a n) (a m)).symm
      (.mk _ _ _ _ (I.restrictInverse h).inv))) (hm h)
  refine ⟨{
    level := J
    levelExact := fun n ↦ ⟨inferInstance, inferInstance⟩
    levelAdjunction := a
    restriction := α
    restrictionMate := ?_ }⟩
  intro m n h
  exact
    ((mateEquiv (a n) (a m)).apply_symm_apply (.mk _ _ _ _ (I.restrictInverse h).inv))

end AlgebraicGeometry
