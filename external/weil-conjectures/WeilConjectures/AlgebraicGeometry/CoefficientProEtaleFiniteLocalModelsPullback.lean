/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback

/-! # Finite local systems on coefficient-sized pro-etale sites
Source: Stacks Tags 03RW and 00VC, inverse image and composition.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
namespace AlgebraicGeometry.ProEtale
private theorem model_preserves {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) := by
  dsimp [Scheme.coefficientProEtaleModelBaseChange]
  have : PreservesFiniteLimits
      (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} Y ⥤ Y.ProEt) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := Y.ProEt)).inverse)
  have : PreservesFiniteLimits (Scheme.proEtaleBaseChange f) := inferInstance
  have : PreservesFiniteLimits
      (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor)
  infer_instance
private def modelComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.coefficientProEtaleModelBaseChange.{u, v} (f ≫ g) ≅
      Scheme.coefficientProEtaleModelBaseChange.{u, v} g ⋙
        Scheme.coefficientProEtaleModelBaseChange.{u, v} f :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g) AsSmall.up)

private def fixedComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (max v (u + 1))) [CommRing A] :
    Scheme.coefficientProEtaleFixedModulePullback.{u, v} (f ≫ g) A ≅
      Scheme.coefficientProEtaleFixedModulePullback.{u, v} g A ⋙
        Scheme.coefficientProEtaleFixedModulePullback.{u, v} f A := by
  let af := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Y) (Scheme.coefficientProEtaleModelTopology X)
  let ag := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} g) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z) (Scheme.coefficientProEtaleModelTopology Y)
  let ac := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} (f ≫ g)) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z) (Scheme.coefficientProEtaleModelTopology X)
  have : (Scheme.coefficientProEtaleModelBaseChange.{u, v} g ⋙
      Scheme.coefficientProEtaleModelBaseChange.{u, v} f).IsContinuous
        (Scheme.coefficientProEtaleModelTopology Z)
        (Scheme.coefficientProEtaleModelTopology X) :=
    Functor.isContinuous_comp _ _ (Scheme.coefficientProEtaleModelTopology Z)
      (Scheme.coefficientProEtaleModelTopology Y) (Scheme.coefficientProEtaleModelTopology X)
  let e := Functor.sheafPushforwardContinuousComp
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} g)
    (Scheme.coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology Z)
    (Scheme.coefficientProEtaleModelTopology Y)
    (Scheme.coefficientProEtaleModelTopology X) ≪≫
      Functor.sheafPushforwardContinuousIso (modelComp.{u, v} f g).symm (ModuleCat A)
        (Scheme.coefficientProEtaleModelTopology Z) (Scheme.coefficientProEtaleModelTopology X)
  exact ((conjugateIsoEquiv ac (ag.comp af)).symm e.symm).symm

/-- Isomorphisms retain the displayed finite constant models on every slice.
Source: Stacks Tag 03RW (auxiliary; not a blueprint node).
Proof: retain the sieve and module and restrict the inverse isomorphism on each slice. -/
theorem coefficientProEtale_finite_iso {T : Scheme.{u}}
    (A : Type (max v (u + 1))) [CommRing A]
    {F G : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} T) (ModuleCat A)}
    (e : F ≅ G) (h : IsCoefficientModelLocallyConstantFinite _ A F) :
    IsCoefficientModelLocallyConstantFinite _ A G := by
  intro V
  obtain ⟨S, hS, ht⟩ := h V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨M, hM, ⟨i⟩⟩ := ht U f hf
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((Scheme.coefficientProEtaleModelTopology.{u, v} T).overPullback
    (ModuleCat A) U).mapIso e.symm ≪≫ i

/-- Finite local models on a stratum persist after a further scheme pullback.
Source: Stacks Tags 03RW and 00VC
(auxiliary; not a blueprint node).
Proof: the two coefficient-site equivalences and scheme base change preserve finite
limits. The general site theorem preserves the same finite local models under inverse
image. Fibre-product pasting identifies composite base change; its direct-image
isomorphism has a unique adjunction mate identifying the two inverse images. Restrict
that isomorphism on every slice and compose with the pulled-back trivialization. -/
theorem coefficientProEtale_finite_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} Z) (ModuleCat A))
    (h : IsCoefficientModelLocallyConstantFinite _ A
      ((Scheme.coefficientProEtaleFixedModulePullback g A).obj F)) :
    IsCoefficientModelLocallyConstantFinite _ A
      ((Scheme.coefficientProEtaleFixedModulePullback (f ≫ g) A).obj F) := by
  have := model_preserves.{u, v} f
  exact coefficientProEtale_finite_iso A ((fixedComp f g A).app F).symm
    (coefficient_finite_local_systems_pullback _ _ _ A _ h)

end AlgebraicGeometry.ProEtale
