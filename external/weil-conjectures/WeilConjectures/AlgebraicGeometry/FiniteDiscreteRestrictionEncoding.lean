/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientSections
/-! # Restriction compatibility of the fixed coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

private local instance restrictionEncodingEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

local instance finiteDiscreteRestrictionEncodingInst1 (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})

local instance finiteDiscreteRestrictionEncodingInst2 (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint

noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

set_option hygiene false in
local notation "ΛB" => Profinite.continuousMapRingObj B

private noncomputable def coefficientUnit (T : Scheme.{u}) :
    A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B) ⟶
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T).obj :=
  (sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ≫
    (finiteDiscreteSchemeRingIso B T eR).hom.hom

private lemma encoding_action (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) (V : T.ProEtᵒᵖ) :
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M))).obj V).X =
    (coefficientUnit B eR T).app V ▷ M.X.obj.obj V ≫
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X).hom.app V := by
  dsimp only [presheafToFunctor, moduleLocalizationRight, Adjunction.modRight,
    Functor.comp_obj]
  simp only [Functor.act_mapMod_obj, Mod.act_comap_obj]
  dsimp only [CategoryTheory.evaluation_obj_map, CategoryTheory.evaluation_obj_obj]
  change (((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ▷ M.X.obj ≫
    Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
      ((presheafToSheaf (ProEt.topology T) Ab.{u + 1}).obj
        (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))) M.X ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      ((finiteDiscreteSchemeRingIso B T eR).hom ▷ M.X) ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X)).app V) = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app,
    coefficientUnit, Category.assoc, comp_whiskerRight]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits
open scoped CategoryTheory.Obj
open Scheme
variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
set_option hygiene false in
local notation "ΛB" => Profinite.continuousMapRingObj B

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

omit [IsMonHom eR.hom] in
private lemma coefficientUnit_pushforward (T U : Scheme.{u}) (j : U ⟶ T)
    (V : T.ProEtᵒᵖ) :
    (coefficientUnit B eR T).app V ≫
      (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app V =
    (coefficientUnit B eR U).app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  exact finiteDiscreteCoefficient_coefficientUnit_pushforward B eR T U j V

private lemma pushforward_tensor (T U : Scheme.{u}) (j : U ⟶ T)
    (P Q : Sheaf (ProEt.topology U) Ab.{u + 1}) (V : T.ProEtᵒᵖ) :
    (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
      (((j)_*[Ab.{u + 1}]).obj P) (((j)_*[Ab.{u + 1}]).obj Q)).app V ≫
      (Functor.LaxMonoidal.μ ((j)_*[Ab.{u + 1}]) P Q).hom.app V =
    (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1}) P Q).app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
  exact @Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    T.ProEt _ U.ProEt _ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j)
    Ab.{u + 1} _ _ _ (ProEt.topology T) (ProEt.topology U)
    (GrothendieckTopology.W.monoidal (J := ProEt.topology T) (A := Ab.{u + 1})) _
    (Scheme.ProEt.isContinuous_overPullback j)
    (GrothendieckTopology.W.monoidal (J := ProEt.topology U) (A := Ab.{u + 1})) _ P Q V

private lemma push_action (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B U) (V : T.ProEtᵒᵖ) :
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj
            ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M)))).obj V).X =
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := U.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology U)
          (A (C := U.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B U eR).hom).obj M))).obj
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)).X := by
  rw [encoding_action B eR T
    ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M) V,
    encoding_action B eR U M
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)]
  let F := (j)_*[Ab.{u + 1}]
  let I := sheafToPresheaf (ProEt.topology T) Ab.{u + 1}
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (condensedRingObj ΛB T) (F.obj M.X)).app V ≫
    (condensedPushforwardHom ΛB j ▷ F.obj M.X ≫
      Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X ≫
      F.map (Mod.act (A := condensedRingObj ΛB U) M.X)).hom.app V = _
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (condensedRingObj ΛB T) (F.obj M.X) ≫
      I.map (condensedPushforwardHom ΛB j ▷ F.obj M.X) ≫
      I.map (Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X) ≫
      I.map (F.map (Mod.act (A := condensedRingObj ΛB U) M.X))).app V = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [NatTrans.comp_app]
  change (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
    (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫
    (Functor.LaxMonoidal.μ I (F.obj (condensedRingObj ΛB U)) (F.obj M.X)).app V ≫
    (Functor.LaxMonoidal.μ F (condensedRingObj ΛB U) M.X).hom.app V ≫
    (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) = _
  have hμ' := pushforward_tensor T U j (condensedRingObj ΛB U) M.X V
  calc
    _ = (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
        (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj ΛB U) M.X).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) ≫
        (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (coefficientUnit B eR T).app V ▷ (F.obj M.X).obj.obj V ≫
          (condensedPushforwardHom ΛB j).hom.app V ▷ (F.obj M.X).obj.obj V ≫ k ≫
          (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)) hμ'
    _ = _ := by
      have hs := coefficientUnit_pushforward B eR T U j V
      have h := congrArg (fun k ↦ k ▷ (F.obj M.X).obj.obj V ≫
        (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology U) Ab.{u + 1})
          (condensedRingObj ΛB U) M.X).app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V) ≫
        (Mod.act (A := condensedRingObj ΛB U) M.X).hom.app
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj V)) hs
      simp only [comp_whiskerRight, Category.assoc] at h
      convert h using 1; rfl

private noncomputable def encodingPushforwardIso (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B U) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj
      ((lowerStar (Profinite.continuousMapRingObj.{u} B) j).obj M) ≅
    ((j)_*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.obj M) := by
  unfold finiteDiscreteCoefficientEquivalence
  apply (fullyFaithfulSheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).preimageIso
  refine NatIso.ofComponents (fun V ↦ ?_) (fun f ↦ ?_)
  · refine G.mapIso (Mod.isoMk (Iso.refl _) ?_)
    simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
    exact push_action B eR T U j M V
  · change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
    rw [← G.map_comp, ← G.map_comp]
    congr 1

private noncomputable def encodingPushforwardNatIso (T U : Scheme.{u}) (j : U ⟶ T) :
    lowerStar (Profinite.continuousMapRingObj.{u} B) j ⋙
        (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse ≅
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse ⋙
        (j)_*[ModuleCat.{u + 1} (ULift.{u + 1} B)] := by
  refine NatIso.ofComponents (encodingPushforwardIso B eR G hG T U j) ?_
  intro M N f
  apply (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1} B))).map_injective
  apply NatTrans.ext
  funext V
  simp only [Functor.map_comp, NatTrans.comp_app, encodingPushforwardIso]
  unfold finiteDiscreteCoefficientEquivalence
  change G.map _ ≫ G.map _ = G.map _ ≫ G.map _
  rw [← G.map_comp, ← G.map_comp]
  congr 1

private noncomputable def encodingPullbackNatIso (T U : Scheme.{u}) (j : U ⟶ T) :
    (finiteDiscreteCoefficientEquivalence B eR G hG T).inverse ⋙
      (j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)] ≅
    upperStar (Profinite.continuousMapRingObj.{u} B) j ⋙
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse := by
  let ET := finiteDiscreteCoefficientEquivalence B eR G hG T
  let EU := finiteDiscreteCoefficientEquivalence B eR G hG U
  let i := encodingPushforwardNatIso B eR G hG T U j
  let k := Iso.isoCompInverse (H := ET.symm) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU.symm) k
  let a := ET.symm.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} B)) j)
  let b := (upperStarLowerStarAdjunction (Profinite.continuousMapRingObj.{u} B) j).comp
    EU.symm.toAdjunction
  exact a.leftAdjointUniq (b.ofNatIsoRight kr)

/-- The common coefficient encoding commutes with inverse image along a scheme morphism.
Source: Bhatt--Scholze, Proposition 5.3.2; the sectionwise encoding of internal
modules and the coefficient identification pulled back from one fixed point.
(blueprint: lem-weil-pbc-finite-discrete-restriction-encoding)

Proof in words. Write the encoding as restriction of scalars along the fixed
constant-ring identification, followed by sectionwise encoding. At the presheaf
level, sectionwise encoding commutes with direct image, which is precomposition;
restriction of scalars commutes with that same precomposition. The coefficient
maps commute because all are obtained by pulling back eR from the profinite point.
Restrict this direct-image isomorphism to sheaves. Conjugating by the two encoding
equivalences and using uniqueness of left adjoints gives the inverse-image
isomorphism. The internal inverse image is mapMod followed by extension of
scalars along condensedPullbackHom. This ring map is invertible, so extension
of scalars is canonically restriction along its inverse. Evaluate the resulting
natural isomorphism at M. This uses no finiteness, nonempty-space, or nonzero-ring
assumption. -/
theorem finiteDiscreteCoefficient_restrictionEncoding
    (T U : Scheme.{u}) (j : U ⟶ T) (M : FiniteDiscreteInternalModules B T) :
    Nonempty (
      ((j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
        ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) ≅
      (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.obj
        ((Mod.comap (inv (condensedPullbackHom
          (Profinite.continuousMapRingObj.{u} B) j))).obj
          ((((j)^*[Ab.{u + 1}]).mapMod
            (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M))) := by
  refine ⟨(encodingPullbackNatIso B eR G hG T U j).app M ≪≫ ?_⟩
  exact (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.mapIso
    ((Mod.extendScalarsIsoComapInv
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j)).app
      ((((j)^*[Ab.{u + 1}]).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M))

end

end AlgebraicGeometry.ProEtale.CondensedRing
