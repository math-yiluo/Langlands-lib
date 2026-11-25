/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusHomEvaluation
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # Section normalization of native Frobenius transport

## References

* Stacks 03D6 and 03EO
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open CategoryTheory.TwistedActionRingedSite
open WeilConjectures.WeilFrobeniusAction
namespace AlgebraicGeometry.ProEtale.NativeFrobenius

open CategoryTheory.Limits MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] Adjunction.rightAdjointLaxMonoidal
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

/-- Pullback along the inverse isomorphism is postcomposition along the isomorphism.

The first pullback projection is an isomorphism; its compatibility with the
structure morphisms is the pullback square followed by `g.inv_hom_id`. -/
noncomputable def pullbackPostcomposeIso (Y : Scheme.{u}) (g : Y ≅ Y) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv ≅ (postcompose g).functor :=
  NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (asIso (pullback.fst V.hom g.inv)) (by
      change pullback.fst V.hom g.inv ≫ (V.hom ≫ g.hom) =
        pullback.snd V.hom g.inv
      rw [← Category.assoc, pullback.condition, Category.assoc, g.inv_hom_id,
        Category.comp_id])) (fun f ↦ by
      ext
      change pullback.lift _ _ _ ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ f.left
      exact pullback.lift_fst _ _ _)

private theorem section_smul (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (M : AdicSheaf l Y) (V : Y.ProEtᵒᵖ) (r : (comparisonRing l Y).obj.obj V)
    (x : ((comparisonModuleFunctor l Y).obj M).val.obj V) :
    (r • x : ((comparisonModuleFunctor l Y).obj M).val.obj V) =
      (Mod.act M.X).hom.app V
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y)
          (WeilCoefficients.{u} l)) (adicConstantSheaf l Y) M.X).app V
            (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)) := by
  rfl

private theorem pushforward_smul (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (M : AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (r : (comparisonRing l Y).obj.obj V)
    (x : ((comparisonModuleFunctor l Y).obj ((adicLowerStar l g.inv).obj M)).val.obj V) :
    (r • x : ((comparisonModuleFunctor l Y).obj ((adicLowerStar l g.inv).obj M)).val.obj V) =
      @SMul.smul
        ((comparisonRing l Y).obj.obj
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V))
        (((comparisonModuleFunctor l Y).obj M).val.obj
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V)) inferInstance
        ((adicConstantSheafToLowerStar l g.inv).hom.app V r) x := by
  change ULift.{u + 1} (PadicAlgCl.locallyFiniteFunctions l V.unop.left) at r
  change M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V) at x
  erw [section_smul]
  change _ = (Mod.act M.X).hom.app _
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y)
      (WeilCoefficients.{u} l)) (adicConstantSheaf l Y) M.X).app _
        (((adicConstantSheafToLowerStar l g.inv).hom.app V r) ⊗ₜ[_] x))
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv) (WeilCoefficients.{u} l)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y)
      (adicConstantSheaf l Y) M.X V
  let U := sheafToPresheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)
  let D := lowerStar (WeilCoefficients.{u} l) g.inv
  let ρ := adicConstantSheafToLowerStar l g.inv
  change ((Functor.LaxMonoidal.μ U (adicConstantSheaf l Y) (D.obj M.X)) ≫
    U.map (ρ ▷ (D.obj M.X) ≫ Functor.LaxMonoidal.μ D _ _ ≫ D.map (Mod.act M.X))).app V
      (r ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x) = _
  rw [U.map_comp, U.map_comp, ← Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  change (Mod.act M.X).hom.app _
    (((Functor.LaxMonoidal.μ U (D.obj (adicConstantSheaf l Y)) (D.obj M.X)).app V ≫
      (Functor.LaxMonoidal.μ D (adicConstantSheaf l Y) M.X).hom.app V)
        (((adicConstantSheafToLowerStar l g.inv).hom.app V r) ⊗ₜ[_] x)) = _
  apply congrArg ((Mod.act M.X).hom.app _)
  exact ConcreteCategory.congr_hom h _

private instance postcomposeContinuous (Y : Scheme.{u}) (g : Y ≅ Y) :
    (postcompose g).functor.IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Y) :=
  Functor.isContinuous_of_iso (pullbackPostcomposeIso Y g) _ _

private noncomputable def postcomposeRingIso (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    ((postcompose g).functor.sheafPushforwardContinuous CommRingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y)).obj (comparisonRing l Y) ≅
        comparisonRing l Y :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

private noncomputable def postcomposeModules (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l Y)) ⥤
      SheafOfModules.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l Y)) :=
  SheafOfModules.pushforward (F := (postcompose g).functor)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology Y)
    (S := (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l Y))
    (R := (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (comparisonRing l Y))
    ((sheafCompose (Scheme.ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (postcomposeRingIso Y l g).inv)

private noncomputable def sectionTranslation (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (M : AdicSheaf l Y) :
    (comparisonModuleFunctor l Y).obj ((adicLowerStar l g.inv).obj M) ≅
      (postcomposeModules Y l g).obj ((comparisonModuleFunctor l Y).obj M) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
  · refine ModuleCat.isoMk
      ((forget₂ (WeilCoefficients.{u} l) AddCommGrpCat).mapIso
        (M.X.obj.mapIso ((pullbackPostcomposeIso Y g).app V.unop).op).symm) ?_
    intro r
    ext x
    symm
    change M.X.obj.map ((pullbackPostcomposeIso Y g).inv.app V.unop).op
        (@SMul.smul _
          (((comparisonModuleFunctor l Y).obj ((adicLowerStar l g.inv).obj M)).val.obj V)
          inferInstance r x) =
      @SMul.smul _
        (((comparisonModuleFunctor l Y).obj M).val.obj ((postcompose g).functor.op.obj V))
        inferInstance r (M.X.obj.map
          ((pullbackPostcomposeIso Y g).inv.app V.unop).op x)
    have h1 := congrArg
      (fun t ↦ M.X.obj.map ((pullbackPostcomposeIso Y g).inv.app V.unop).op t)
      (pushforward_smul Y l g M V r x)
    have h2 := ((comparisonModuleFunctor l Y).obj M).val.map_smul
      ((pullbackPostcomposeIso Y g).inv.app V.unop).op
        ((adicConstantSheafToLowerStar l g.inv).hom.app V r) x
    have hr : (comparisonRing l Y).obj.map
        ((pullbackPostcomposeIso Y g).inv.app V.unop).op
          ((adicConstantSheafToLowerStar l g.inv).hom.app V r) = r := by
      exact ConcreteCategory.congr_hom
        ((comparisonRing l Y).obj.mapIso
          ((pullbackPostcomposeIso Y g).app V.unop).op).hom_inv_id r
    exact (h1.trans h2).trans
      (congrArg (fun a ↦ @SMul.smul _
        (((comparisonModuleFunctor l Y).obj M).val.obj ((postcompose g).functor.op.obj V))
        inferInstance a (M.X.obj.map
          ((pullbackPostcomposeIso Y g).inv.app V.unop).op x)) hr)
  · intro V W f
    ext x
    change M.X.obj.map ((pullbackPostcomposeIso Y g).inv.app W.unop).op
        (M.X.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.map f) x) =
      M.X.obj.map ((postcompose g).functor.op.map f)
        (M.X.obj.map ((pullbackPostcomposeIso Y g).inv.app V.unop).op x)
    have h := congrArg (fun t ↦ M.X.obj.map t.op)
      ((pullbackPostcomposeIso Y g).inv.naturality f.unop)
    exact (ConcreteCategory.congr_hom
      (M.X.obj.map_comp
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.map f)
        ((pullbackPostcomposeIso Y g).inv.app W.unop).op) x).symm.trans
      ((ConcreteCategory.congr_hom h x).symm.trans
        (ConcreteCategory.congr_hom
          (M.X.obj.map_comp ((pullbackPostcomposeIso Y g).inv.app V.unop).op
            ((postcompose g).functor.op.map f)) x))

private noncomputable def smallTranslation (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y) ⋙
      postcomposeModules Y l g ≅
      sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g) ⋙
        SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y) := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  exact Iso.refl _

private theorem sectionTranslation_hom_app (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (M : AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (z : ((adicLowerStar l g.inv).obj M).X.obj.obj V) :
    (sectionTranslation Y l g M).hom.val.app V z =
      M.X.obj.map ((pullbackPostcomposeIso Y g).inv.app V.unop).op z := by
  rfl

private noncomputable def sectionTranslationIso (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    adicLowerStar l g.inv ⋙ (adicSectionModuleEquivalence l Y).functor ≅
      (adicSectionModuleEquivalence l Y).functor ⋙ postcomposeModules Y l g :=
  NatIso.ofComponents (sectionTranslation Y l g) (fun {M N} f ↦ by
    ext V x
    change (sectionTranslation Y l g N).hom.val.app V
        (f.hom.hom.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V) x) =
      f.hom.hom.app ((postcompose g).functor.op.obj V)
        ((sectionTranslation Y l g M).hom.val.app V x)
    simp only [sectionTranslation_hom_app]
    exact ConcreteCategory.congr_hom
      (f.hom.hom.naturality ((pullbackPostcomposeIso Y g).inv.app V.unop).op).symm x)

private noncomputable def sectionConjugate (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    ((equivalence Y l).functor ⋙ adicLowerStar l g.inv) ⋙
        (adicSectionModuleEquivalence l Y).functor ≅
      (sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g) ⋙
        (equivalence Y l).functor) ⋙ (adicSectionModuleEquivalence l Y).functor := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  let E := adicSectionModuleEquivalence l Y
  let Q := SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y) (comparisonRing l Y)
  let S := sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)
  let F := (equivalence Y l).functor
  let e : F ⋙ E.functor ≅ Q := sectionCounit Y l
  exact
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (sectionTranslationIso Y l g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e (postcomposeModules Y l g) ≪≫
      smallTranslation Y l g ≪≫
      Functor.isoWhiskerLeft S e.symm ≪≫
      (Functor.associator _ _ _).symm

private noncomputable def translationIso (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    (equivalence Y l).functor ⋙ adicLowerStar l g.inv ≅
      sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g) ⋙
        (equivalence Y l).functor := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (adicSectionModuleEquivalence l Y).functor).whiskeringRight _).preimageIso
      (sectionConjugate Y l g)

private theorem translationIso_map (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    ∀ M : Modules (ring Y l),
      (comparisonModuleFunctor l Y).map ((translationIso Y l g).hom.app M) =
        (sectionConjugate Y l g).hom.app M := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  dsimp only
  intro M
  exact (Functor.FullyFaithful.ofFullyFaithful
    (adicSectionModuleEquivalence l Y).functor).map_preimage _

private theorem translationIso_sections (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    ∀ (M : Modules (ring Y l)) (V : Y.ProEtᵒᵖ)
      (z : ((adicLowerStar l g.inv).obj ((equivalence Y l).functor.obj M)).X.obj.obj V),
      ((sectionCounit Y l).hom.app
        ((sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)).obj M)).val.app V
          (((translationIso Y l g).hom.app M).hom.hom.app V z) =
      ((sectionCounit Y l).hom.app M).val.app ((postcompose g).functor.op.obj V)
        (((equivalence Y l).functor.obj M).X.obj.map
          ((pullbackPostcomposeIso Y g).inv.app V.unop).op z) := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  dsimp only
  intro M V z
  have h := congrArg (fun k ↦ k.val.app V z) (translationIso_map Y l g M)
  change ((translationIso Y l g).hom.app M).hom.hom.app V z =
    ((sectionCounit Y l).inv.app
      ((sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)).obj M)).val.app V
        (((sectionCounit Y l).hom.app M).val.app ((postcompose g).functor.op.obj V)
          (((equivalence Y l).functor.obj M).X.obj.map
            ((pullbackPostcomposeIso Y g).inv.app V.unop).op z)) at h
  rw [h]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app V) ((sectionCounit Y l).app
      ((sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)).obj M)).inv_hom_id) _

/-- The concrete native translation isomorphism, with its section normalization. -/
theorem nativeFrobeniusSectionTransport (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    ∃ c : (equivalence Y l).functor ⋙ adicLowerStar l g.inv ≅
        sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g) ⋙
          (equivalence Y l).functor,
      ∀ (M : Modules (ring Y l)) (V : Y.ProEtᵒᵖ)
        (z : ((adicLowerStar l g.inv).obj ((equivalence Y l).functor.obj M)).X.obj.obj V),
      ((sectionCounit Y l).hom.app
        ((sigma (topology Y) (translation g) (ring Y l) (ringIso Y l g)).obj M)).val.app V
          ((c.hom.app M).hom.hom.app V z) =
      ((sectionCounit Y l).hom.app M).val.app ((postcompose g).functor.op.obj V)
        (((equivalence Y l).functor.obj M).X.obj.map
          ((pullbackPostcomposeIso Y g).inv.app V.unop).op z) := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  dsimp only
  exact ⟨translationIso Y l g, translationIso_sections Y l g⟩

end AlgebraicGeometry.ProEtale.NativeFrobenius
