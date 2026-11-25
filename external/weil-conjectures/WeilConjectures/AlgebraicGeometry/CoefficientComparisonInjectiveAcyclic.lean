/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineSections
import all WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
/-! # Injective acyclicity for intrinsic coefficient comparison
Source: Stacks Tags 099U and 099V.
-/
@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme
open CategoryTheory.Functor.sheafPullbackConstruction

private theorem smallModelAbUnitIso (X : Scheme.{u}) :
    IsIso (sheafAdjunctionContinuous (Scheme.smallModelComparisonInclusion.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).unit := by
  let A := AddCommGrpCat.{max v (u + 1)}
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.IsDenseSubsite
      J X.smallEtaleTopology := by
    change (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).inducedTopology
        X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.IsDenseSubsite
      K (ProEt.topology X) := by
    change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).IsDenseSubsite
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt).inducedTopology
        (ProEt.topology X)) (ProEt.topology X)
    infer_instance
  let eE : Sheaf X.smallEtaleTopology A ≌ Sheaf J A :=
    Equivalence.sheafCongr X.smallEtaleTopology J
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)) A
  let eP : Sheaf (Scheme.ProEt.topology X) A ≌ Sheaf K A :=
    Equivalence.sheafCongr (Scheme.ProEt.topology X) K
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)) A
  let L := sheafPullback (Scheme.toProEt X) A X.smallEtaleTopology (ProEt.topology X)
  let adjL := sheafAdjunctionContinuous (Scheme.toProEt X) A
    X.smallEtaleTopology (ProEt.topology X)
  have : IsIso adjL.unit := additiveUnitIso.{u, v} X
  have : L.Faithful := adjL.faithful_L_of_mono_unit_app
  have : L.Full := adjL.full_L_of_isSplitEpi_unit_app
  let adj := eE.symm.toAdjunction.comp (adjL.comp eP.toAdjunction)
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let R := (Scheme.toProEt X).sheafPushforwardContinuous A
    X.smallEtaleTopology (ProEt.topology X)
  let qR : (eP.inverse ⋙ R) ⋙ eE.functor ≅ F.sheafPushforwardContinuous A J K :=
    NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (Iso.refl _))
      (by intro M N f; ext U; rfl)
  have ha : (eE.inverse ⋙ L ⋙ eP.functor) ⊣
      F.sheafPushforwardContinuous A J K := by
    exact adj.ofNatIsoRight qR
  let q := ha.leftAdjointUniq (sheafAdjunctionContinuous F A J K)
  have : (sheafPullback F A J K).Faithful := Functor.Faithful.of_iso q
  have : (sheafPullback F A J K).Full := Functor.Full.of_iso q
  exact (sheafAdjunctionContinuous F A J K).unit_isIso_of_L_fully_faithful

private theorem intrinsicUnitIso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    [HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}] :
    IsIso (SheafOfModules.pullbackPushforwardAdjunction
      (F := Scheme.smallModelComparisonInclusion.{u, v} X)
      (constructibleComparisonRingMap.{u, v} X A)).unit := by
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
  obtain ⟨e, he⟩ := SheafOfModules.inverseImage_underlying_unit_of_ring_presentation
    (F := F) (constructibleComparisonRingMap X A) pr hpr
  have : IsIso (sheafAdjunctionContinuous F AddCommGrpCat.{max v (u + 1)} J K).unit :=
    smallModelAbUnitIso X
  let canonical := SheafOfModules.pullbackPushforwardAdjunction
    (F := F) (constructibleComparisonRingMap X A)
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  change IsIso (canonical.unit.app M)
  have hmap : IsIso ((SheafOfModules.toSheaf _).map (canonical.unit.app M)) := by
    have hc := he M
    have : IsIso ((SheafOfModules.toSheaf _).map
        (canonical.unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{max v (u + 1)} J K).map
          (e.hom.app M)) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((F.sheafPushforwardContinuous AddCommGrpCat.{max v (u + 1)} J K).map (e.hom.app M))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (canonical.unit.app M)
    (SheafOfModules.toSheaf _) hmap inferInstance

/-- The ordinary comparison unit is invertible on injectives, whose inverse images
are acyclic for comparison direct image. The sheafification, enough-injectives and additive
instances only specify the ordinary derived-functor constructions; they exist
canonically on the two small sites. Any adjunction between the fixed functors
has the asserted unit property.
Source: Stacks Tags 099U and 099V; blueprint bounded-below comparison
(auxiliary; not a blueprint node).

Proof: transport constant-ring modules through the constant-scalar and AsSmall
site equivalences. The constant-section ring map identifies the intrinsic unit
with the ordinary comparison unit, which is invertible. This is independent of
the choice of adjunction between the fixed functors. On an affine etale object,
restriction preserves injectives because it has exact extension by zero as a
left adjoint. The ind-etale affine basis admits compatible refinements by inverse
limits of finite-stage etale coverings, with their nerves descending to a common
stage. Each augmented module Cech complex is exact on an injective; exact filtered
colimits preserve this exactness. The basis Cech criterion therefore gives the
positive cohomology vanishing of the pullback on every affine etale object.
Applying the direct image to an injective resolution and sheafifying these local
computations gives vanishing of every positive right-derived direct image. All
transport functors are exact equivalences and preserve injectivity and this
vanishing. This uses neither finiteness of A nor nonemptiness of X. -/
theorem coefficientComparison_injectiveAcyclic (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    [HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)}]
    [EnoughInjectives (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))]
    [(SheafOfModules.pushforward.{max v (u + 1)}
      (F := Scheme.smallModelComparisonInclusion.{u, v} X)
      (constructibleComparisonRingMap.{u, v} X A)).Additive]
    (adj : constructibleComparisonPullback.{u, v} X A ⊣
      SheafOfModules.pushforward.{max v (u + 1)}
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap.{u, v} X A)) :
    ∀ (I : ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)) [Injective I],
      IsIso (adj.unit.app I) ∧
      (SheafOfModules.pushforward.{max v (u + 1)}
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
        (constructibleComparisonRingMap.{u, v} X A)).rightAcyclic
          ((constructibleComparisonPullback.{u, v} X A).obj I) := by
  intro I _
  have hunit := intrinsicUnitIso X A
  let canonical := SheafOfModules.pullbackPushforwardAdjunction
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap.{u, v} X A)
  have : IsIso canonical.unit := hunit
  have : (constructibleComparisonPullback.{u, v} X A).Full :=
    canonical.full_L_of_isSplitEpi_unit_app
  have : (constructibleComparisonPullback.{u, v} X A).Faithful :=
    canonical.faithful_L_of_mono_unit_app
  have : IsIso adj.unit := adj.unit_isIso_of_L_fully_faithful
  refine ⟨inferInstance, ?_⟩
  intro q
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let B := AddCommGrpCat.{max v (u + 1)}
  let R := SheafOfModules.pushforward.{max v (u + 1)}
    (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap.{u, v} X A)
  let V := SheafOfModules.toSheaf.{max v (u + 1)}
    (siteModuleRings (ConstantCompletion.constant J A))
  let resolution := injectiveResolution ((constructibleComparisonPullback.{u, v} X A).obj I)
  refine IsZero.of_iso ?_ (resolution.isoRightDerivedObj R (q + 1))
  rw [HomologicalComplex.homologyFunctor_obj,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  let S := (R.mapHomologicalComplex (.up ℕ)).obj resolution.cocomplex |>.sc (q + 1)
  change S.Exact
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  have : (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.IsDenseSubsite
      J X.smallEtaleTopology := by
    change (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsDenseSubsite
      ((AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).inducedTopology
        X.smallEtaleTopology) X.smallEtaleTopology
    infer_instance
  let eE : Sheaf X.smallEtaleTopology B ≌ Sheaf J B :=
    Equivalence.sheafCongr X.smallEtaleTopology J
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)) B
  let Φa := (AffineEtale.Spec X).sheafPushforwardContinuous B (AffineEtale.topology X)
    X.smallEtaleTopology
  have : Φa.Additive := ⟨rfl⟩
  have : Φa.PreservesHomology := {}
  have : PreservesFiniteColimits V := (moduleSheaves_colimits_forgetful _).2.2.1
  have : V.PreservesHomology := {}
  let Φ := V ⋙ eE.inverse ⋙ Φa
  have : Φ.Additive := Functor.additive_of_preserves_binary_products Φ
  have : Φ.PreservesHomology := {}
  rw [← S.exact_map_iff_of_faithful Φ]
  let T := (S.map Φ).map (sheafToPresheaf (AffineEtale.topology X) B)
  have hT : T.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro W
    have h := (coefficientComparison_affineSections_vanishing X A I W.unop q).of_iso
      (resolution.isoRightDerivedObj _ (q + 1)).symm
    rw [HomologicalComplex.homologyFunctor_obj,
      ← HomologicalComplex.exactAt_iff_isZero_homology] at h
    exact h
  have : (presheafToSheaf (AffineEtale.topology X) B).PreservesHomology := {}
  have hT' := hT.map (presheafToSheaf (AffineEtale.topology X) B)
  refine (ShortComplex.exact_iff_of_iso ?_).1 hT'
  exact (ShortComplex.mapNatIso (S.map Φ) (sheafificationNatIso _ _)).symm
end AlgebraicGeometry.ProEtale
