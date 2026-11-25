/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization

/-! # Closed direct image preserves coefficient-sized etale origin

Source: Stacks Project, proetale.tex, Tags 09A6, 09AA.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

private def fixedSiteAdjunction {C D : Type w} [SmallCategory C] [SmallCategory D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [G.IsContinuous J K] (A : Type w) [CommRing A] :
    Functor.sheafPullbackConstruction.sheafPullback G (ModuleCat.{w} A) J K ⊣
      G.sheafPushforwardContinuous (ModuleCat.{w} A) J K :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G (ModuleCat.{w} A) J K

private theorem fixedSiteHasKernel {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A]
    {M N : Sheaf J (ModuleCat.{w} A)} (f : M ⟶ N) : HasKernel f := by
  exact @HasLimitsOfShape.has_limit WalkingParallelPair inferInstance _ inferInstance
    (HasFiniteLimits.out WalkingParallelPair) (parallelPair f 0)

@[instance_reducible] private def fixedSiteAbelian {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A] :
    Abelian (Sheaf J (ModuleCat.{w} A)) := inferInstance

@[instance_reducible] private def intrinsicSiteAbelian {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type w) [CommRing A] :
    Abelian (ConstantCompletion.Mod (ConstantCompletion.constant J A)) := inferInstance

private theorem scalarEquiv {C : Type*} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type _) [CommRing A] :
    (coefficientModelFixedScalars J A).IsEquivalence :=
  coefficientModelFixedScalars_isEquivalence J A

private theorem fixedRingMap_unit (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.constantCoefficientUnit
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≫
      (constructibleComparisonRingMap.{u, v} X A).hom =
    Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, v} X).op
      (SheafOfModules.constantCoefficientUnit
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let F := Scheme.smallModelComparisonInclusion.{u, v} X
  let φ := Functor.whiskerLeft F.op
    (toSheafify K ((Functor.const _).obj (CommRingCat.of A)))
  have h := ((sheafificationAdjunction J CommRingCat.{max v (u + 1)}).homEquiv
    ((Functor.const _).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{max v (u + 1)} J K).obj
      (ConstantCompletion.constant K A))).apply_symm_apply φ
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})) h

private def fixedPushforwardSquare (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    SheafOfModules.pushforward (constructibleComparisonRingMap.{u, v} X A) ⋙
        coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ⋙
        (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
          (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext x
    have h := congrArg (fun f ↦ f.app V a) (fixedRingMap_unit X A)
    exact congrArg (fun b ↦ b • (show M.val.obj
      ((Scheme.smallModelComparisonInclusion.{u, v} X).op.obj V) from x)) h.symm
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

private def comparisonFixedLeft (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    constructibleComparisonPullback.{u, v} X A ⋙
        coefficientModelFixedScalars (Scheme.coefficientProEtaleModelTopology.{u, v} X) A ≅
      coefficientModelFixedScalars (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A ⋙
        Functor.sheafPullbackConstruction.sheafPullback
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have := scalarEquiv (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalarEquiv (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let E := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let G := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  let adjM := SheafOfModules.pullbackPushforwardAdjunction
    (constructibleComparisonRingMap.{u, v} X A)
  let adjO := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let a := adjM.comp G.toAdjunction
  let b := E.toAdjunction.comp adjO
  let R := SheafOfModules.pushforward (constructibleComparisonRingMap.{u, v} X A)
  let S := (Scheme.smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  let h : (G.inverse ⋙ R) ⋙ E.functor ≅ S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G.inverse (fixedPushforwardSquare X A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.counitIso S ≪≫ Functor.leftUnitor S
  let h' : (S ⋙ E.inverse) ⋙ E.functor ≅ S :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft S E.counitIso ≪≫
      Functor.rightUnitor S
  let r := ((Functor.FullyFaithful.ofFullyFaithful E.functor).whiskeringRight _)
    |>.preimageIso (h ≪≫ h'.symm)
  exact ((conjugateIsoEquiv a b).symm r).symm

private theorem closed_continuousIso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    {F G : X.ProEtᵒᵖ ⥤ ModuleCat.{max v (u + 1)} A} (e : F ≅ G)
    (hF : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P F)) :
    ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P G) := by
  intro I _ _ P
  have := hF P
  have hn := continuityMap_natural P e.hom
  have : IsIso (Functor.whiskerLeft P.diagram.op e.hom) := by
    change IsIso (Functor.isoWhiskerLeft P.diagram.op e).hom
    infer_instance
  apply (isIso_comp_left_iff
    (colimMap (Functor.whiskerLeft P.diagram.op e.hom)) _).mp
  rw [hn]
  infer_instance

private def closedPresentation {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
    (P : AffinePresentation X I) : AffinePresentation Z I where
  diagram := P.diagram ⋙ Scheme.proEtaleBaseChange i
  affine k := by
    have : IsAffine ((𝟭 Scheme).obj (P.diagram.obj k).left) := P.affine k
    change IsAffine (pullback (P.diagram.obj k).hom i)
    have : IsAffineHom (pullback.fst (P.diagram.obj k).hom i) := inferInstance
    exact isAffine_of_isAffineHom (pullback.fst (P.diagram.obj k).hom i)
  etale k := by
    have := P.etale k
    exact inferInstanceAs (Etale (pullback.snd (P.diagram.obj k).hom i))
  cone := (Scheme.proEtaleBaseChange i).mapCone P.cone
  affineVertex := by
    have : IsAffine ((𝟭 Scheme).obj P.cone.pt.left) := P.affineVertex
    change IsAffine (pullback P.cone.pt.hom i)
    have : IsAffineHom (pullback.fst P.cone.pt.hom i) := inferInstance
    exact isAffine_of_isAffineHom (pullback.fst P.cone.pt.hom i)
  isLimit := isLimitOfPreserves (Over.pullback i) P.isLimit

/-- Closed direct image takes a classical sheaf to a classical sheaf, with independent
coefficient size. No finite-generation, finite-set or Noetherian condition is imposed.
Source: Stacks Project, Tag 09A6, lemma-morphism-comparison, in degree zero;
Tag 09AA, lemma-closed-immersion
(auxiliary; not a blueprint node).

Proof: pull any affine etale presentation over X back along i. Its stages and
vertex remain affine because a closed immersion and all its base changes are
affine, and its stage structure maps remain etale. Base change is a right adjoint
on the over-categories, so the pulled-back cone is still a limit. For an etale
antecedent G of H, the comparison continuity theorem says that its section cocone
on this presentation over Z is a colimit. This is exactly the section cocone of
the direct image on the original presentation over X. Naturality transports the
colimit and invertibility of the continuity maps through the given isomorphism.

The inverse constant-scalar equivalence sends that direct image to an intrinsic
constant-ring module. Its counit identifies the underlying fixed-scalar sheaf with
the original direct image, so its continuity maps are invertible too. Apply the
existing classical-module origin criterion, then the fixed-comparison isomorphism
and the scalar-equivalence counit to obtain the required etale antecedent. Every
construction keeps the A-action and takes place in max v (u+1). The pulled-back
affine presentation works also for empty Z and full-image closed immersions that
are not scheme isomorphisms. -/
theorem coefficientFixed_closed_directImage_essImage
    (A : Type (max v (u + 1))) [CommRing A]
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (H : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} Z)
      (ModuleCat.{max v (u + 1)} A))
    (hH : (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} Z) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} Z)
      (Scheme.coefficientProEtaleModelTopology.{u, v} Z)).essImage H) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).essImage
      (((Scheme.coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
      (ModuleCat.{max v (u + 1)} A) (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} Z)).obj H) := by
  have := scalarEquiv (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A
  have := scalarEquiv (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
  let eE := (coefficientModelFixedScalars
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A).asEquivalence
  let eP := (coefficientModelFixedScalars
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).asEquivalence
  let push := (Scheme.coefficientProEtaleModelBaseChange.{u, v} i).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.coefficientProEtaleModelTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} Z)
  let Y := push.obj H
  have hY : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          Y.obj)) := by
    obtain ⟨G, ⟨e⟩⟩ := hH
    apply closed_continuousIso.{u, v} X A
      (Functor.isoWhiskerLeft
        (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op
        ((sheafToPresheaf _ _).mapIso (push.mapIso e)))
    intro I _ _ P
    obtain ⟨hc⟩ := coefficientFixedComparison_isColimit.{u, v} Z A G (closedPresentation i P)
    change IsIso (colimit.desc _ _)
    exact inferInstanceAs (IsIso ((colimit.isColimit _).coconePointUniqueUpToIso hc).hom)
  have hM : ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
      (P : AffinePresentation X I), IsIso (continuityMap P
        ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
          (eP.functor.obj (eP.inverse.obj Y)).obj)) :=
    closed_continuousIso.{u, v} X A
      (Functor.isoWhiskerLeft
        (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op
        ((sheafToPresheaf _ _).mapIso (eP.counitIso.app Y).symm)) hY
  obtain ⟨G, ⟨e⟩⟩ := coefficientClassicalModule_origin.{u, v} X A (eP.inverse.obj Y) hM
  refine ⟨eE.functor.obj G, ⟨?_⟩⟩
  exact ((comparisonFixedLeft.{u, v} X A).app G).symm ≪≫ eP.functor.mapIso e ≪≫
    eP.counitIso.app Y

end AlgebraicGeometry.ProEtale
