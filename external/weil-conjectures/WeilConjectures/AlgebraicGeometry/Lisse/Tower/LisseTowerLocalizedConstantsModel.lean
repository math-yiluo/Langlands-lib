/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.CoefficientSheafificationSquare.CoefficientSheafificationIso
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! # Constant models for localized fixed realization

This is the model-existence part of the localized constant realization.

## Implementation details

The model is built from the ordinary constant-sheaf comparison given by the constant-sheaf and
inverse-image adjunctions, transported through the finite coefficient comparison, applied
termwise to complexes and localized; it is natural in the algebraic complex.

## References

* Stacks Project, Modules on Sites, Tags 03CY and 03DA
* Sites, Tag 0H7J
* Cohomology on Sites, Tag 06YY
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/- Constant module presheaves are left adjoint to evaluation at a terminal object. -/
private abbrev constantModulePresheaf
    {C : Type (u + 1)} [Category.{u} C] (B : Type (u + 1)) [CommRing B] :=
  (Functor.const Cᵒᵖ) ⋙ ProEtale.finiteCoefficientModulePresheaf C B

private def constantModulePresheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] (B : Type (u + 1)) [CommRing B]
    (V : C) (hV : IsTerminal V) :
    constantModulePresheaf (C := C) B ⊣
      PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of B)) (op V) where
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
  left_triangle_components M := by ext W x; rfl
  right_triangle_components P := by
    ext x
    change P.map (hV.from V).op x = x
    have h : hV.from V = 𝟙 V := hV.hom_ext _ _
    rw [h]
    exact congrArg (fun f ↦ f x) (P.map_id (op V))

private abbrev constantPresentation
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {B : Type (u + 1)} [CommRing B] {R : Sheaf J RingCat.{u + 1}}
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :=
  constantModulePresheaf (C := C) B ⋙ PresheafOfModules.sheafification a

private abbrev presentationSections
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {B : Type (u + 1)} [CommRing B] {R : Sheaf J RingCat.{u + 1}}
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj) (V : C) :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars a ⋙
    PresheafOfModules.evaluation _ (op V)

private def presentationAdjunction
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {B : Type (u + 1)} [CommRing B] {R : Sheaf J RingCat.{u + 1}}
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (V : C) (hV : IsTerminal V) :
    constantPresentation a ⊣ presentationSections a V :=
  (constantModulePresheafAdjunction B V hV).comp
    (PresheafOfModules.sheafificationAdjunction a)

/- Sheafifying first in fixed coefficients gives the same module presentation. -/
private def fixedConstantSeed
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B : Type (u + 1)) [CommRing B] [HasSheafify J (ModuleCat.{u + 1} B)]
    (M : ModuleCat.{u + 1} B) :
    (constantModulePresheaf (C := C) B).obj M ⟶
      (ProEtale.finiteCoefficientModulePresheaf C B).obj
        (((constantSheaf J (ModuleCat.{u + 1} B)).obj M).obj) :=
  (ProEtale.finiteCoefficientModulePresheaf C B).map
    (toSheafify J ((Functor.const Cᵒᵖ).obj M))

private def fixedConstantIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B : Type (u + 1)} [CommRing B] {R : Sheaf J RingCat.{u + 1}}
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J (ModuleCat.{u + 1} B)] [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [J.PreservesSheafification (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})] :
    constantPresentation a ≅ constantSheaf J (ModuleCat.{u + 1} B) ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        ProEtale.finiteCoefficientModulePresheaf C B ⋙
          PresheafOfModules.sheafification a) := by
  let t : constantPresentation a ⟶ constantSheaf J (ModuleCat.{u + 1} B) ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} B) ⋙
        ProEtale.finiteCoefficientModulePresheaf C B ⋙
          PresheafOfModules.sheafification a) :=
    { app M := (PresheafOfModules.sheafification a).map (fixedConstantSeed J B M)
      naturality M N f := by
        change (PresheafOfModules.sheafification a).map
            ((ProEtale.finiteCoefficientModulePresheaf C B).map
              ((Functor.const Cᵒᵖ).map f)) ≫ _ = _
        simpa only [Functor.map_comp, fixedConstantSeed, Functor.comp_map,
          Functor.id_map, constantSheaf, toSheafification_app] using congrArg
          (fun k ↦ (PresheafOfModules.sheafification a).map
            ((ProEtale.finiteCoefficientModulePresheaf C B).map k))
          ((toSheafification J (ModuleCat.{u + 1} B)).naturality
            ((Functor.const Cᵒᵖ).map f)) }
  have ht (M : ModuleCat.{u + 1} B) : IsIso (t.app M) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)]
    change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
        (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})))
    rw [← J.W_iff]
    exact J.W_of_preservesSheafification _ _ (J.W_toSheafify _)
  have : IsIso t := (NatTrans.isIso_iff_isIso_app t).mpr ht
  exact asIso t

/- Compare left adjoints using global sections with their actual scalar actions. -/
private def presentationPullIso {X Z : Scheme.{u}} (g : Z ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {B : Type (u + 1)} [CommRing B]
    (α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶ ((adicLisseForget X).obj R).obj)
    (β : (Functor.const Z.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((adicLisseForget Z).obj ((adicTowerInverseImage g).obj R)).obj)
    [Presheaf.IsLocallyInjective (ProEt.topology X) α]
    [Presheaf.IsLocallySurjective (ProEt.topology X) α]
    [Presheaf.IsLocallyInjective (ProEt.topology Z) β]
    [Presheaf.IsLocallySurjective (ProEt.topology Z) β]
    (h : α ≫ Functor.whiskerRight
        ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange g).op β) :
    constantPresentation α ⋙ proEtaleRingModulePullback g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ≅ constantPresentation β := by
  let V : X.ProEt := ⊤_ X.ProEt
  let hV : IsTerminal V := terminalIsTerminal
  let adj := (presentationAdjunction α V hV).comp
    (proEtaleRingModuleOperations_properties g R
      ((adicTowerInverseImage g).obj R) (Iso.refl _)).2.2.2.2.some
  let e : proEtaleRingModuleDirectImage g R
        ((adicTowerInverseImage g).obj R) (Iso.refl _) ⋙ presentationSections α V ≅
      presentationSections β ((proEtaleBaseChange g).obj V) := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · let r := ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app R).hom.app (op V)
      have hr : (β.app (op ((proEtaleBaseChange g).obj V))).hom =
          r.hom.comp (α.app (op V)).hom := by
        exact congrArg RingCat.Hom.hom (congr_app h (op V)).symm
      exact (ModuleCat.restrictScalarsComp'App (α.app (op V)).hom r.hom
        (β.app (op ((proEtaleBaseChange g).obj V))).hom hr
          (N.val.obj (op ((proEtaleBaseChange g).obj V)))).symm
    · intro M N f
      ext x
      rfl
  let hZ : IsTerminal ((proEtaleBaseChange g).obj V) :=
    hV.isTerminalObj (proEtaleBaseChange g) V
  exact (adj.ofNatIsoRight e).leftAdjointUniq
    (presentationAdjunction β ((proEtaleBaseChange g).obj V) hZ)

private def adicConstantPresentationIso (X : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    constantPresentation (adicLisseConstantUnit X B) ≅ adicLisseConstantModules X B := by
  let H : ModuleCat.{u + 1} B ⥤
      PresheafOfModules.{u + 1} ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of B)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) B ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const X.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of B))
  let t : constantModulePresheaf (C := X.ProEt) B ≅ H := by
    refine NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
      (fun V ↦ ?_) ?_) ?_
    · exact (LinearEquiv.refl B M).toModuleIso
    · intro V W f
      ext x
      rfl
    · intro M N f
      ext V x
      rfl
  exact Functor.isoWhiskerRight t
    (PresheafOfModules.sheafification (adicLisseConstantUnit X B))

/- Changing an isomorphic ring presentation commutes with module sheafification. -/
private def presentationTransportIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {B : Type (u + 1)} [CommRing B] {R S : Sheaf J RingCat.{u + 1}}
    (e : R ≅ S)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (h : β = α ≫ e.hom.hom) :
    constantPresentation α ≅ constantPresentation β ⋙ SheafOfModules.restrictScalars e.hom := by
  let t : constantModulePresheaf (C := C) B ≅ constantModulePresheaf (C := C) B ⋙
      CoefficientSheafificationSquare.rawRestriction (RingHom.id B) :=
    NatIso.ofComponents (fun M ↦ PresheafOfModules.isoMk
      (fun V ↦ (ModuleCat.restrictScalarsId B).symm.app M)
      (by intros; ext x; rfl)) (by intros; ext V x; rfl)
  exact Functor.isoWhiskerRight t (PresheafOfModules.sheafification α) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (constantModulePresheaf (C := C) B)
      (CoefficientSheafificationSquare.rawIso J (RingHom.id B) e.hom α β
        (by simpa using h)) ≪≫ (Functor.associator _ _ _).symm

private def fixedProEtaleConstantIso {X Z : Scheme.{u}} (g : Z ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} B) ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} B) g ≅
      constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B) := by
  let hX : IsTerminal (⊤_ X.ProEt) := terminalIsTerminal
  let hZ := hX.isTerminalObj (proEtaleBaseChange g) _
  let adj := ((constantSheafAdj (ProEt.topology X) (ModuleCat.{u + 1} B) hX).comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g)).ofNatIsoRight
      (Iso.refl _)
  exact adj.leftAdjointUniq (constantSheafAdj (ProEt.topology Z) (ModuleCat.{u + 1} B) hZ)

private def sourceScalarMap (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :=
  adicLisseConstantUnit X (A ⧸ d.ideal ^ (n + 1)) ≫
    ((adicLisseForget X).map (pbcLevelConstantComparison X d n).hom).hom

private instance sourceScalarMap_injective (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Presheaf.IsLocallyInjective (ProEt.topology X) (sourceScalarMap X d n) := by
  unfold sourceScalarMap
  infer_instance

private instance sourceScalarMap_surjective (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    Presheaf.IsLocallySurjective (ProEt.topology X) (sourceScalarMap X d n) := by
  unfold sourceScalarMap
  infer_instance

private def sourcePresentationIso (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    constantPresentation (sourceScalarMap X d n) ≅
      adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1)) ⋙
        pbcRestrict (pbcLevelConstantComparison X d n).inv := by
  let e := (adicLisseForget X).mapIso (pbcLevelConstantComparison X d n).symm
  exact presentationTransportIso (ProEt.topology X) e (sourceScalarMap X d n)
      (adicLisseConstantUnit X (A ⧸ d.ideal ^ (n + 1)))
      (by
        unfold sourceScalarMap
        rw [Category.assoc]
        change _ = _ ≫ ((adicLisseForget X).map (pbcLevelConstantComparison X d n).hom).hom ≫
          ((adicLisseForget X).map (pbcLevelConstantComparison X d n).inv).hom
        rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id]
        rfl) ≪≫
    Functor.isoWhiskerRight (adicConstantPresentationIso X (A ⧸ d.ideal ^ (n + 1))) _

/- The chosen finite coefficient isomorphism respects the constant-ring units. -/
private theorem sourceScalarMap_pull {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    sourceScalarMap X d n ≫ Functor.whiskerRight
        ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app
          ((pbcAdicRings X d).obj (op n))).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) =
      Functor.whiskerLeft (proEtaleBaseChange g).op (lisseTowerFiniteScalarMap g d n) := by
  let B := A ⧸ d.ideal ^ (n + 1)
  let R := (pbcAdicRings X d).obj (op n)
  let C := adicLisseConstantRing X B
  let k := pbcLevelConstantComparison X d n
  let e := lisseTowerFiniteCoefficientIso g d n
  let adj := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let ρ := proEtaleConstantDirectImageMap g CommRingCat.{u + 1} (CommRingCat.of B)
  have he : adj.unit.app R ≫ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map e.hom =
      k.inv ≫ ρ := by
    change adj.homEquiv R _ e.hom = _
    dsimp only [e, lisseTowerFiniteCoefficientIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, asIso_hom]
    rw [adj.homEquiv_naturality_left]
    change k.inv ≫ adj.homEquiv C _ ((adj.homEquiv C _).symm ρ) = _
    rw [Equiv.apply_symm_apply]
  have hρ : toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of B)) ≫ ρ.hom =
      Functor.whiskerLeft (proEtaleBaseChange g).op
        (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj
          (CommRingCat.of B))) := by
    exact ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      _ _).apply_symm_apply _
  have hke : k.hom ≫ adj.unit.app R ≫
      (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map e.hom = ρ := by
    rw [he, Iso.hom_inv_id_assoc]
  have hke' : k.hom.hom ≫ (adj.unit.app R).hom ≫
      ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).map e.hom).hom = ρ.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using
      congrArg (fun φ ↦ φ.hom) hke
  have hinv : ((adicLisseForget Z).map e.inv).hom ≫
      ((adicLisseForget Z).map e.hom).hom = 𝟙 _ := by
    simpa only [Functor.mapIso_inv, Functor.mapIso_hom,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom] using
      congrArg (fun φ ↦ φ.hom) ((adicLisseForget Z).mapIso e).inv_hom_id
  apply (cancel_mono (Functor.whiskerLeft (proEtaleBaseChange g).op
    (((adicLisseForget Z).map e.hom).hom))).mp
  dsimp only [sourceScalarMap, lisseTowerFiniteScalarMap]
  rw [Functor.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [← Functor.whiskerLeft_comp, hinv, Functor.whiskerLeft_id', Category.comp_id]
  change Functor.whiskerRight
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)) ≫
      k.hom.hom ≫ (adj.unit.app R).hom ≫
        ((proEtaleSheafDirectImage g CommRingCat.{u + 1}).map e.hom).hom)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) = _
  rw [hke', hρ]
  rfl

/- Assemble the constant model before passing to complexes and localization. -/
private def ordinaryConstantModel {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ⋙
        lisseTowerFixedSheafRealization g d n ≅
      constantAdicQuotientModules X d n ⋙ proEtaleRingModulePullback g
        ((pbcAdicRings X d).obj (op n))
        ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _) := by
  let q := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (constantAdicQuotientMap d.ideal n)
  let C := constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
  let F := lisseTowerFiniteSheafRealization g d n
  let P := proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)
  let α := sourceScalarMap X d n
  let β := lisseTowerFiniteScalarMap g d n
  let i : C ⋙ sheafCompose (ProEt.topology Z) q ≅
      q ⋙ constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) :=
    constantCommuteCompose (ProEt.topology Z) q
  letI : (ProEt.topology Z).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1))) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction (ProEt.topology Z)
      (ModuleCat.forget₂CoinduceAdj _)
  let j := fixedConstantIso (ProEt.topology Z) β
  let k := presentationPullIso g ((pbcAdicRings X d).obj (op n)) α β
    (sourceScalarMap_pull g d n)
  exact (Functor.associator C _ F).symm ≪≫ Functor.isoWhiskerRight i F ≪≫
    Functor.associator q _ F ≪≫ Functor.isoWhiskerLeft q j.symm ≪≫
    Functor.isoWhiskerLeft q k.symm ≪≫
    Functor.isoWhiskerLeft q (Functor.isoWhiskerRight (sourcePresentationIso X d n) P) ≪≫
    (Functor.associator q _ P).symm

private def derivedConstantModel {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    normalizationConstant (ProEt.topology Z) ⋙ lisseTowerFixedRealization g d n ≅
      constantAdicQuotientRealization g d n := by
  unfold constantAdicQuotientRealization
  let C := constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
  let F := lisseTowerFixedSheafRealization g d n
  let P := proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
    ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n))) (Iso.refl _)
  exact Functor.isoWhiskerLeft C.mapDerivedCategory (lisseTowerFixedRealizationIso g d n).symm ≪≫
    Functor.mapDerivedCategoryCompIso C F ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryConstantModel g d n) ≪≫
    (Functor.mapDerivedCategoryCompIso (constantAdicQuotientModules X d n) P).symm

private def derivedFixedConstantPullIso {X Z : Scheme.{u}} (g : Z ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    normalizationConstant (ProEt.topology X) ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory ≅
      normalizationConstant (ProEt.topology Z) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (fixedProEtaleConstantIso g B)

private def derivedComparisonConstantIso (S : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :
    normalizationConstant S.smallEtaleTopology ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) S).mapDerivedCategory ≅
      normalizationConstant (ProEt.topology S) :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (ProEtale.constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} B) S)

/-- Constant complexes admit localized fixed-realization models. -/
theorem lisseTower_localized_constants_model
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d j
    Nonempty (∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (L n).obj ((localProEtaleComparison a
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization g d n).obj E) := by
  refine ⟨fun n E ↦ ?_⟩
  let B := lisseTowerEtaleRing d n
  let e₁ := (derivedComparisonConstantIso S B).app E
  let e₂ := (derivedFixedConstantPullIso a B).app E
  let e₃ := (derivedFixedConstantPullIso b B).app E
  exact (lisseTowerFixedRealization g d n).mapIso
      ((ProEtale.upperStar (ModuleCat.{u + 1} B) b).mapDerivedCategory.mapIso
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) a).mapDerivedCategory.mapIso e₁ ≪≫ e₂) ≪≫
          e₃) ≪≫ (derivedConstantModel g d n).app E

end AlgebraicGeometry.Scheme
