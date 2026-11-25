/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Canonical comparison of the two completed coefficient rings

Source: Stacks Tags 00YY and 03CY; Bhatt--Scholze, Proposition 6.6.11.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The small-site precomposition is an equivalence.
Source: Stacks Tag 00YY (auxiliary; not a blueprint node). -/
instance sfbDown_isEquivalence (T : Scheme.{u}) :
    (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤ T.ProEt).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv (C := T.ProEt)).inverse.IsEquivalence)

/-- The induced topology makes the equivalent small site a dense subsite.
Source: Stacks Tag 00YY (auxiliary; not a blueprint node). -/
instance sfbDown_isDenseSubsite (T : Scheme.{u}) :
    (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤ T.ProEt).IsDenseSubsite
      (coefficientProEtaleModelTopology.{u, 0} T) (ProEt.topology T) := by
  change (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤ T.ProEt).IsDenseSubsite
    ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤
      T.ProEt).inducedTopology (ProEt.topology T)) (ProEt.topology T)
  infer_instance

/-- The equivalent-site precomposition preserves coverings in the reverse direction.
Source: Stacks Tag 00YY (auxiliary; not a blueprint node). -/
instance sfbDown_isCocontinuous (T : Scheme.{u}) :
    (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤ T.ProEt).IsCocontinuous
      (coefficientProEtaleModelTopology.{u, 0} T) (ProEt.topology T) := by
  let := sfbDown_isDenseSubsite T
  infer_instance

attribute [-instance] SheafOfModules.instAbelian in
/-- Precomposition to the equivalent small site is additive.
Source: Stacks Tag 03CY (auxiliary; not a blueprint node). -/
instance sfbModuleToModel_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel.{u} (X := X) R).Additive := by
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The canonical constant sheafification comparison under the equivalent small site.
Source: Stacks Tags 00YY and 03CY
(auxiliary; not a blueprint node). -/
def sfbModelConstantsIso (T : Scheme.{u}) :
    constantSheaf (ProEt.topology T) CommRingCat.{u + 1} ⋙
      (AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤ T.ProEt).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientProEtaleModelTopology.{u, 0} T) (ProEt.topology T) ≅
      constantSheaf (coefficientProEtaleModelTopology.{u, 0} T) CommRingCat.{u + 1} :=
  NatIso.ofComponents (fun A ↦
    ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤
      T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{u + 1} (coefficientProEtaleModelTopology.{u, 0} T) (ProEt.topology T)).symm.app
          ((Functor.const T.ProEtᵒᵖ).obj A)) (by
    intro A B f
    exact ((AsSmall.down : coefficientProEtaleSiteModel.{u, 0} T ⥤
      T.ProEt).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{u + 1} (coefficientProEtaleModelTopology.{u, 0} T)
          (ProEt.topology T)).inv.naturality
          ((Functor.const T.ProEtᵒᵖ).map f))

attribute [local irreducible] sfbModelConstantsIso

/-- The constant comparison, naturally in the positive quotient exponent.
Source: Stacks Tags 00YY and 03CY
(auxiliary; not a blueprint node). -/
def sfbModelSystemIso (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    adicLisseRingSystem T I ⋙ sfbModelRings T ≅
      ConstantCompletion.finiteSystem (coefficientProEtaleModelTopology.{u, 0} T) A I := by
  refine NatIso.ofComponents (fun n ↦ (sfbModelConstantsIso T).app
    (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))) ?_
  intro n m f
  change (sfbModelRings T).map ((adicLisseRingSystem T I).map f) ≫ _ = _
  let hn := (NatTrans.ofOpSequence
    (F := adicLisseRingSystem T I ⋙ sfbModelRings T)
    (G := ConstantCompletion.finiteSystem (coefficientProEtaleModelTopology.{u, 0} T) A I) (fun n ↦
    (sfbModelConstantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1)) )) (by
      intro n
      simpa only [Functor.comp_map, adicLisseRingSystem,
        ConstantCompletion.finiteSystem, Functor.ofOpSequence_map_homOfLE_succ,
        ConstantCompletion.transition] using (sfbModelConstantsIso T).hom.naturality
        (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n + 1)))))
  exact hn.naturality f
attribute [local irreducible] sfbModelSystemIso

/-- The limit comparison for the actual positive quotient diagrams.
Source: Stacks Tags 00YY and 03CY
(auxiliary; not a blueprint node). -/
def sfbModelCompletionIso (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) :
    (sfbModelRings T).obj (adicLisseCompletedRing T I) ≅
      ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, 0} T) A I :=
  preservesLimitIso (sfbModelRings T) (adicLisseRingSystem T I) ≪≫
    lim.mapIso (sfbModelSystemIso T I)

attribute [local irreducible] sfbModelCompletionIso

/-- The limit comparison commutes with every actual quotient projection.
Source: Stacks Tags 00YY and 03CY
(auxiliary; not a blueprint node). -/
theorem sfbModelCompletionIso_projection (T : Scheme.{u}) {A : Type (u + 1)}
    [CommRing A] (I : Ideal A) (n : ℕ) :
    (sfbModelCompletionIso T I).hom ≫
        ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, 0} T) A I n =
      (sfbModelRings T).map (limit.π (adicLisseRingSystem T I) (op n)) ≫
        (sfbModelConstantsIso T).hom.app (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
  unfold sfbModelCompletionIso
  change ((preservesLimitIso (sfbModelRings T) (adicLisseRingSystem T I)).hom ≫
    lim.map (sfbModelSystemIso T I).hom) ≫ _ = _
  erw [Category.assoc, limMap_π, ← Category.assoc, preservesLimitIso_hom_π]
  unfold sfbModelSystemIso
  rfl

end AlgebraicGeometry.Scheme
