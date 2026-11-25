/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientClassicalSingle
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived localization of canonical coefficient comparison

Source: Stacks Tags 00YV, 03D2 and 09AL. The constant-ring presentation argument
is the existing proof from ConstructibleComparisonModuleExact, without its cyclic
import through the constructible comparison theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.ProEtale
open Scheme

section ConstantPresentation
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K]
  {W : C} (hW : IsTerminal W) (hFW : IsTerminal (F.obj W))
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def constantPullbackIso (A : Type u) :
    (constantSheaf K (Type u)).obj A ≅
      (sheafPullback F (Type u) J K).obj ((constantSheaf J (Type u)).obj A) :=
  ((conjugateIsoEquiv
    ((constantSheafAdj J (Type u) hW).comp
      (sheafAdjunctionContinuous F (Type u) J K))
    (constantSheafAdj K (Type u) hFW)).symm
      (F.sheafPushforwardContinuousCompSheafSectionsObjIso (Type u) J K (op W))).app A
private theorem constantPullback_unit (A : Type u) :
    ((sheafificationAdjunction K (Type u)).unit.app ((Functor.const Dᵒᵖ).obj A)).app
        (op (F.obj W)) ≫
      (constantPullbackIso F J K hW hFW A).hom.hom.app (op (F.obj W)) =
    ((sheafificationAdjunction J (Type u)).unit.app ((Functor.const Cᵒᵖ).obj A)).app (op W) ≫
      ((sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((constantSheaf J (Type u)).obj A)).hom.app (op W) := by
  have h := unit_conjugateEquiv_symm
    ((constantSheafAdj J (Type u) hW).comp
      (sheafAdjunctionContinuous F (Type u) J K))
    (constantSheafAdj K (Type u) hFW)
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso (Type u) J K (op W)).hom A
  simpa [constantPullbackIso, constantSheafAdj, Adjunction.comp_unit_app,
    Functor.sheafPushforwardContinuousCompSheafSectionsObjIso] using h.symm

private theorem constantPullback_unit_all (A : Type u) (U : Cᵒᵖ) :
    (toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) ≫
      (constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U ≫
      ((sheafAdjunctionContinuous F (Type u) J K).unit.app
        ((constantSheaf J (Type u)).obj A)).hom.app U := by
  let a := (toSheafify K ((Functor.const Dᵒᵖ).obj A)) ≫
    (constantPullbackIso F J K hW hFW A).hom.hom
  let b := toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫
    ((sheafAdjunctionContinuous F (Type u) J K).unit.app
      ((constantSheaf J (Type u)).obj A)).hom
  have ha := a.naturality (F.op.map (hW.from U.unop).op)
  have hb := b.naturality (hW.from U.unop).op
  change a.app (F.op.obj U) = a.app (op (F.obj W)) ≫ _ at ha
  change b.app U = b.app (op W) ≫ _ at hb
  have ht := constantPullback_unit F J K hW hFW A
  change a.app (op (F.obj W)) = b.app (op W) at ht
  simpa only [a, b, NatTrans.comp_app] using
    ha.trans ((congrArg (fun z ↦ z ≫ _) ht).trans hb.symm)

private theorem constantForget_unit (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] :
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
        (forget CommRingCat.{u}) ≫
      ((constantCommuteCompose J (forget CommRingCat.{u})).app (CommRingCat.of A)).hom.hom =
        toSheafify J ((Functor.const Cᵒᵖ).obj A) := by
  change Functor.whiskerRight
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
    (forget CommRingCat.{u}) ≫
      ((constantCommuteCompose J (forget CommRingCat.{u})).hom.app
        (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac]
  rw [← toSheafify_naturality]
  rfl

private def canonicalRingMap (A : Type u) [CommRing A] :
    (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A) ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
        ((constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A)) :=
  ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm
    (Functor.whiskerLeft F.op (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))))

include hW hFW in
private theorem ringPresentation (A : Type u) [CommRing A] :
    ∃ pr : SheafPullbackUnitPresentation (F := F)
      ((sheafCompose J (forget CommRingCat.{u})).obj
        ((constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)))
      ((sheafCompose K (forget CommRingCat.{u})).obj
        ((constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A))),
      pr.unit = (sheafCompose J (forget CommRingCat.{u})).map
        (canonicalRingMap F J K A) := by
  let R := (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of A)
  let S := (constantSheaf K CommRingCat.{u}).obj (CommRingCat.of A)
  let UJ := sheafCompose J (forget CommRingCat.{u})
  let UK := sheafCompose K (forget CommRingCat.{u})
  let eJ := (constantCommuteCompose J (forget CommRingCat.{u})).app (CommRingCat.of A)
  let eK := (constantCommuteCompose K (forget CommRingCat.{u})).app (CommRingCat.of A)
  let L := sheafPullback F (Type u) J K
  let adj := sheafAdjunctionContinuous F (Type u) J K
  let φ := canonicalRingMap F J K A
  let e : UK.obj S ≅ L.obj (UJ.obj R) :=
    eK ≪≫ constantPullbackIso F J K hW hFW A ≪≫ L.mapIso eJ.symm
  let φs : UJ.obj R ⟶ (F.sheafPushforwardContinuous (Type u) J K).obj (UK.obj S) :=
    UJ.map φ
  refine ⟨⟨φs, e, ?_⟩, rfl⟩
  have hφ : toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ φ.hom =
      Functor.whiskerLeft F.op (toSheafify K
        ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))) := by
    exact ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).apply_symm_apply _
  have he : φs ≫ (F.sheafPushforwardContinuous (Type u) J K).map e.hom =
      adj.unit.app (UJ.obj R) := by
    apply (cancel_epi eJ.inv).mp
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ ((F.sheafPushforwardContinuous (Type u) J K).obj
      (L.obj (UJ.obj R))).property
    ext U a
    have hj := congrArg (fun t ↦ t.app U a) (constantForget_unit J A)
    have hk := congrArg (fun t ↦ t.app (F.op.obj U) a) (constantForget_unit K A)
    have hp := congrArg (fun t ↦ t.app U a) hφ
    have hc := congrArg (fun t ↦ t a)
      (constantPullback_unit_all F J K hW hFW A U)
    have hn := congrArg (fun t ↦ t.hom.app U)
      (adj.unit.naturality eJ.inv)
    dsimp only [NatTrans.comp_app] at hj hk hp hc
    have hiJ : eJ.inv.hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) =
          (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a := by
      have hj' : eJ.hom.hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) =
            (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := hj
      exact (congrArg (fun x ↦ eJ.inv.hom.app U x) hj').symm.trans
        (ConcreteCategory.congr_hom
          (congrArg (fun t ↦ t.hom.app U) eJ.hom_inv_id) _)
    change (L.map eJ.inv).hom.app (F.op.obj U)
      ((constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U)
        (eK.hom.hom.app (F.op.obj U)
          (φ.hom.app U (eJ.inv.hom.app U
            ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))))) =
      (adj.unit.app (UJ.obj R)).hom.app U
        (eJ.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a))
    rw [hiJ]
    change (φ.hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U) a at hp
    rw [hp]
    change eK.hom.hom.app (F.op.obj U)
      ((toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))).app (F.op.obj U) a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) a at hk
    rw [hk]
    change (constantPullbackIso F J K hW hFW A).hom.hom.app (F.op.obj U)
      ((toSheafify K ((Functor.const Dᵒᵖ).obj A)).app (F.op.obj U) a) =
        (adj.unit.app ((constantSheaf J (Type u)).obj A)).hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a) at hc
    rw [hc]
    have hh := ConcreteCategory.congr_hom hn
      ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)
    change (adj.unit.app (UJ.obj R)).hom.app U
      (eJ.inv.hom.app U ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)) = _ at hh
    rw [hiJ] at hh
    exact hh.symm
  intro U x
  exact congrArg (fun t ↦ t.hom.app U x) he

end ConstantPresentation

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem comparisonLeftAdjoint (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    (constructibleComparisonPullback X A).IsLeftAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap X A)).isLeftAdjoint

-- Override the successor-universe-only source instance locally in this section.
private instance (priority := 100000) largeAbSheafify {C : Type*} [Category C]
    [EssentiallySmall.{w} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{w} := by
  let e := equivSmallModel.{w} C
  have : HasSheafify (e.inverse.inducedTopology J) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  exact e.hasSheafify J (e.inverse.inducedTopology J) _

private theorem comparisonUnderlying (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    Nonempty (constructibleComparisonPullback X A ⋙ SheafOfModules.toSheaf _ ≅
        SheafOfModules.toSheaf _ ⋙
          sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
            AddCommGrpCat.{max v (u + 1)}
            (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
            (Scheme.coefficientProEtaleModelTopology.{u, v} X)) := by
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have : PreservesFiniteLimits F := by
    dsimp [F, Scheme.smallModelComparisonInclusion]
    infer_instance
  let W := ⊤_ (Scheme.smallModelComparisonEtaleSite.{u, v} X)
  have hW : IsTerminal W := terminalIsTerminal
  have hFW : IsTerminal (F.obj W) := hW.isTerminalObj F W
  have : RepresentablyFlat F := by
    dsimp [F, Scheme.smallModelComparisonInclusion]
    infer_instance
  obtain ⟨pr, hpr⟩ := ringPresentation F J K hW hFW A
  obtain ⟨e, _⟩ := SheafOfModules.inverseImage_underlying_unit_of_ring_presentation
    (F := F) (constructibleComparisonRingMap X A) pr hpr
  exact ⟨e⟩

private theorem liftExact {C D : Type w} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (F : ConstantCompletion.Mod R ⥤ ConstantCompletion.Mod S)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ∃ L : ConstantCompletion.D R ⥤ ConstantCompletion.D S,
      Nonempty (ConstantCompletion.Q R ⋙ L ≅
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ ConstantCompletion.Q S) ∧
      (∀ q : ℤ, Nonempty (L ⋙ coefficientModelCohomology S q ≅
        coefficientModelCohomology R q ⋙ F)) ∧
      Nonempty (coefficientModelSingle R 0 ⋙ L ≅ F ⋙ coefficientModelSingle S 0) := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  let := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  refine ⟨F.mapDerivedCategory, ⟨F.mapDerivedCategoryFactors⟩,
    fun q ↦ ⟨(F.mapDerivedCategoryHomologyFunctorIso q).symm⟩,
    ?_⟩
  unfold coefficientModelSingle
  exact ⟨F.mapDerivedCategorySingleFunctor 0⟩

/-- The actual canonical inverse image descends to the ordinary derived categories.
No constructibility or boundedness hypothesis is needed for this ambient functor.
Source: Stacks Tags 00YV, 03D2 and 09AL
(auxiliary; not a blueprint node).

Proof: the constant-sheaf adjunction identifies the pullback constant ring with the
specified pro-etale constant ring, and its unit is the constant-section map defining
our inverse image. The module inverse-image comparison identifies the underlying
additive sheaf with the additive inverse image. Representable flatness gives left
exactness there, and the conservative module forgetful functor reflects finite
limits. The module pullback is a left adjoint, so preserves finite colimits and
zero morphisms; left exactness then gives additivity. The exact-functor localization
of Mathlib sends quasi-isomorphisms to isomorphisms and supplies the displayed
natural factorization through the standard derived localization. -/
theorem constructibleComparison_derivedFunctor (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    ∃ D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      Nonempty (ConstantCompletion.Q _ ⋙ D ≅
        constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _) ∧
      (∀ q : ℤ, Nonempty (D ⋙ coefficientModelCohomology _ q ≅
        coefficientModelCohomology _ q ⋙ constructibleComparisonPullback X A)) ∧
      Nonempty (coefficientModelSingle _ 0 ⋙ D ≅
        constructibleComparisonPullback X A ⋙ coefficientModelSingle _ 0) := by
  let F := constructibleComparisonPullback X A
  have : F.IsLeftAdjoint := comparisonLeftAdjoint X A
  let V := SheafOfModules.toSheaf.{max v (u + 1)} (siteModuleRings
    (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
  let L := sheafPullback (Scheme.smallModelComparisonInclusion.{u, v} X)
    AddCommGrpCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_functor
  have : RepresentablyFlat (Scheme.smallModelComparisonInclusion.{u, v} X) := by
    dsimp [Scheme.smallModelComparisonInclusion]
    infer_instance
  have : PreservesFiniteLimits L := by
    dsimp [L]
    infer_instance
  obtain ⟨e⟩ := comparisonUnderlying X A
  have : PreservesFiniteLimits (F ⋙ V) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F V
  have : PreservesFiniteColimits F := inferInstance
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  exact liftExact _ _ F
end AlgebraicGeometry.ProEtale
