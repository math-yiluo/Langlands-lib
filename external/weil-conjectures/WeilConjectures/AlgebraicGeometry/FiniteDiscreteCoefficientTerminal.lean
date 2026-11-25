/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing

/-! # The coefficient comparison at the base-changed terminal object -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_finiteDiscreteCoefficientTerminal
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

section UnitComparison
open Opposite
variable {C D A : Type*} [Category C] [Category D] [Category A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [F.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]

private theorem constantPullback_unit {W : C} (hW : IsTerminal W)
    (hFW : IsTerminal (F.obj W)) (M : A) :
    ((sheafificationAdjunction K A).unit.app ((Functor.const Dᵒᵖ).obj M)).app
        (op (F.obj W)) ≫
      ((constantPullbackMonoidalIso F J K hW hFW).hom.app M).hom.app
        (op (F.obj W)) =
    ((sheafificationAdjunction J A).unit.app ((Functor.const Cᵒᵖ).obj M)).app (op W) ≫
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).unit.app
        ((constantSheaf J A).obj M)).hom.app (op W) := by
  have h := unit_conjugateEquiv_symm
    ((constantSheafAdj J A hW).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K))
    (constantSheafAdj K A hFW) (pushforwardSectionsIso (A := A) F J K W).hom M
  have hi (G : Sheaf K A) :
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F A J K).inv.app G = 𝟙 _ := by
    have hh :=
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F A J K).inv_hom_id_app G
    rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
      Category.comp_id] at hh
    exact hh
  simpa [constantPullbackMonoidalIso, constantSheafAdj, Adjunction.comp_unit_app,
    pushforwardSectionsIso, precomposeEvaluationIso, hi] using h.symm

private theorem constantPullback_unit_map {W : C} (hW : IsTerminal W)
    (hFW : IsTerminal (F.obj W)) (M : A) (G : Sheaf J A)
    (a : (constantSheaf J A).obj M ⟶ G) :
    ((sheafificationAdjunction K A).unit.app ((Functor.const Dᵒᵖ).obj M) ≫
      ((constantPullbackMonoidalIso F J K hW hFW).hom.app M ≫
        (Functor.sheafPullbackConstruction.sheafPullback F A J K).map a).hom).app
          (op (F.obj W)) =
      (((sheafificationAdjunction J A).unit.app ((Functor.const Cᵒᵖ).obj M)).app (op W) ≫
        a.hom.app (op W)) ≫
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).unit.app G).hom.app
          (op W) := by
  have hu := constantPullback_unit F J K hW hFW M
  have hn := congrArg (fun f ↦ f.hom.app (op W))
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).unit.naturality a)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.id_map, Functor.comp_map,
    Functor.sheafPushforwardContinuous_map_hom_app] at hn ⊢
  rw [← Category.assoc, hu, Category.assoc]
  simpa only [Category.assoc] using congrArg (fun k ↦
    ((sheafificationAdjunction J A).unit.app ((Functor.const Cᵒᵖ).obj M)).app (op W) ≫ k)
      hn.symm

private theorem constant_naturality {P : Cᵒᵖ ⥤ A} {M : A}
    (q : (Functor.const Cᵒᵖ).obj M ⟶ P) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    q.app X ≫ P.map f = q.app Y := by
  simpa using (q.naturality f).symm

private theorem coefficient_comp {M X Y Z Y' Z' : A}
    (q0 : M ⟶ X) (uT : X ⟶ Y) (uU : X ⟶ Y') (η : Y ⟶ Z)
    (c₁ : Y' ⟶ Z') (c₂ : Z' ⟶ Z)
    (qT : M ⟶ Y) (qU : M ⟶ Y') (qU' : M ⟶ Z)
    (hT : qT = q0 ≫ uT) (hU : qU = q0 ≫ uU)
    (hc : uT ≫ η = uU ≫ c₁ ≫ c₂) (hr : (qU ≫ c₁) ≫ c₂ = qU') :
    qT ≫ η = qU' := by
  rw [hT, Category.assoc, hc, ← Category.assoc, ← Category.assoc, ← hU, hr]

end UnitComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

private theorem constant_lowerStarComp (M : Ab.{u + 1}) (T U : Scheme.{u}) (j : U ⟶ T)
    (H : Sheaf (ProEt.topology U) Ab.{u + 1})
    (q : (Functor.const U.ProEtᵒᵖ).obj M ⟶ H.obj) (W : specZ.{u}.ProEt) :
    (q.app (Opposite.op
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ U)).obj W)) ≫
        ((eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ j).symm)).app H).hom.app
          (Opposite.op W)) ≫
        ((lowerStarComp Ab.{u + 1} j (toSpecZ T)).inv.app H).hom.app (Opposite.op W) =
    q.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
      (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W))) := by
  rw [eqToHom_lowerStar_app_hom_app Ab.{u + 1} (comp_toSpecZ j).symm,
    lowerStarComp_inv_app_hom_app]
  have hn₁ := constant_naturality q
    (((MorphismProperty.Over.pullbackCongr (comp_toSpecZ j)).hom.app W).op)
  have hn₂ := constant_naturality q
    (((MorphismProperty.Over.pullbackComp j (toSpecZ T)).inv.app W).op)
  exact (congrArg (fun f ↦ f ≫ H.obj.map
    (((MorphismProperty.Over.pullbackComp j (toSpecZ T)).inv.app W).op)) hn₁).trans hn₂

private theorem terminal_coefficient_of_units (M : Ab.{u + 1})
    (T U : Scheme.{u}) (j : U ⟶ T)
    (G : Sheaf (ProEt.topology specZ.{u}) Ab.{u + 1})
    (HT : Sheaf (ProEt.topology T) Ab.{u + 1})
    (HU : Sheaf (ProEt.topology U) Ab.{u + 1})
    (rT : G ⟶ (toSpecZ T)_*[Ab.{u + 1}].obj HT)
    (rU : G ⟶ (toSpecZ U)_*[Ab.{u + 1}].obj HU)
    (c : HT ⟶ (j)_*[Ab.{u + 1}].obj HU)
    (qT : (Functor.const T.ProEtᵒᵖ).obj M ⟶ HT.obj)
    (qU : (Functor.const U.ProEtᵒᵖ).obj M ⟶ HU.obj)
    (W : specZ.{u}.ProEt) (q0 : M ⟶ G.obj.obj (Opposite.op W))
    (hT : qT.app (Opposite.op
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W)) =
        q0 ≫ rT.hom.app (Opposite.op W))
    (hU : qU.app (Opposite.op
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ U)).obj W)) =
        q0 ≫ rU.hom.app (Opposite.op W))
    (hc : rT ≫ (toSpecZ T)_*[Ab.{u + 1}].map c =
      rU ≫ (eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ j).symm)).app HU ≫
        (lowerStarComp Ab.{u + 1} j (toSpecZ T)).inv.app HU) :
    qT.app (Opposite.op
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W)) ≫
      c.hom.app (Opposite.op
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W)) =
    qU.app ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
      (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj W))) := by
  have hc' := congrArg (fun f ↦ f.hom.app (Opposite.op W)) hc
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app] at hc'
  exact coefficient_comp q0 _ _ _ _ _ _ _ _ hT hU hc'
    (constant_lowerStarComp M T U j HU qU W)

private theorem coefficient_unit_comp
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (T U : Scheme.{u}) (j : U ⟶ T) :
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T)).unit.app
        (pointUpperStar.obj R) ≫
      (toSpecZ T)_*[Ab.{u + 1}].map (condensedPushforwardHom R j) =
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ U)).unit.app
        (pointUpperStar.obj R) ≫
      (eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ j).symm)).app _ ≫
        (lowerStarComp Ab.{u + 1} j (toSpecZ T)).inv.app
          ((toSpecZ U)^*[Ab.{u + 1}].obj (pointUpperStar.obj R)) := by
  rw [← unitAlgHom_comp_map_condensedPullbackHom, Functor.map_comp,
    condensedPullbackHom_eq]
  exact unit_comp_lowerStar_map_unit_comp_upperStarComp Ab.{u + 1}
    j (toSpecZ U) (toSpecZ T) (comp_toSpecZ j) (pointUpperStar.obj R)

private theorem constantScheme_pushforward (M : Ab.{u + 1})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (e : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj M ⟶ R)
    (T U : Scheme.{u}) (j : U ⟶ T) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj M) ≫
      ((constantSchemeIso T).hom.app M ≫ (upperStarFromPoint T).map e).hom).app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) ≫
      (condensedPushforwardHom R j).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj M) ≫
      ((constantSchemeIso U).hom.app M ≫ (upperStarFromPoint U).map e).hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
          (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
            (proEtTerminal specZ.{u})))) := by
  let W := proEtTerminal specZ.{u}
  let a : (constantSheaf (ProEt.topology specZ.{u}) Ab.{u + 1}).obj M ⟶
      pointUpperStar.obj R :=
    constantPointIso.hom.app M ≫ pointUpperStar.map e
  let q0 := ((sheafificationAdjunction (ProEt.topology specZ.{u}) Ab.{u + 1}).unit.app
    ((Functor.const specZ.{u}.ProEtᵒᵖ).obj M)).app (Opposite.op W) ≫
      a.hom.app (Opposite.op W)
  have hq (X : Scheme.{u}) :
      ((sheafificationAdjunction (ProEt.topology X) Ab.{u + 1}).unit.app
          ((Functor.const X.ProEtᵒᵖ).obj M) ≫
        ((constantSchemeIso X).hom.app M ≫ (upperStarFromPoint X).map e).hom).app
          (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj W)) =
        q0 ≫ ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).unit.app
          (pointUpperStar.obj R)).hom.app (Opposite.op W) := by
    have hu := constantPullback_unit_map (A := Ab.{u + 1})
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X))
      (ProEt.topology specZ.{u}) (ProEt.topology X)
      (proEtIsTerminal W) (proEtIsTerminal
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj W))
      M (pointUpperStar.obj R) a
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, constantSchemeIso,
      Iso.app_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    simp only [q0, a, upperStarFromPoint, upperStarLowerStarAdjunction,
      Functor.comp_map, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, Category.assoc, ObjectProperty.FullSubcategory.id_hom,
      NatTrans.id_app, Category.comp_id] at hu ⊢
    exact hu
  exact terminal_coefficient_of_units M T U j (pointUpperStar.obj R)
    ((toSpecZ T)^*[Ab.{u + 1}].obj (pointUpperStar.obj R))
    ((toSpecZ U)^*[Ab.{u + 1}].obj (pointUpperStar.obj R))
    ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T)).unit.app _)
    ((upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ U)).unit.app _)
    (condensedPushforwardHom R j)
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      ((Functor.const T.ProEtᵒᵖ).obj M) ≫
      ((constantSchemeIso T).hom.app M ≫ (upperStarFromPoint T).map e).hom)
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
      ((Functor.const U.ProEtᵒᵖ).obj M) ≫
      ((constantSchemeIso U).hom.app M ≫ (upperStarFromPoint U).map e).hom)
    W q0 (hq T) (hq U) (coefficient_unit_comp R T U j)

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits
open scoped CategoryTheory.Obj
open Scheme
variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- The coefficient comparison commutes with direct image at the base change of the
terminal object of the pro-etale site of Spec Z.
Source: Bhatt--Scholze, Proposition 5.3.2; the inverse-image composition adjunction.
(blueprint: lem-weil-pbc-finite-discrete-coefficient-terminal)

Proof in words. Put W = proEtTerminal Spec Z and W_X = pi_X^* W. The conjugation
unit law for constantPullbackMonoidalIso identifies the sheafification unit followed
by finiteDiscreteSchemeRingIso on W_X with q0 followed by the unit of pi_X^*.
Here q0 is the constant sheafification unit on Spec Z followed by constantPointIso
and pointUpperStar applied to eR. This formula follows from unit_conjugateEquiv_symm
and naturality of the inverse-image adjunction unit in eR. Apply
unit_comp_map_condensedPushforwardHom at W and precompose with q0. Its right-hand
side is the coefficient map on W_U followed by the restrictions for pullbackCongr
(comp_toSpecZ j) and pullbackComp j (toSpecZ T). Each restriction disappears by
naturality of a map from a constant presheaf: q(Y) = q(X) followed by restriction
along X to Y. Applying this twice gives the displayed equality at j^* W_T.
This uses no nonemptiness, finiteness, discreteness or nonzero-ring hypothesis. -/
theorem finiteDiscreteCoefficient_coefficientUnit_pushforward_terminal
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (T U : Scheme.{u}) (j : U ⟶ T) :
    ((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B T eR).hom.hom).app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) ≫
        (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} B) j).hom.app
        (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u}))) =
    ((sheafificationAdjunction (ProEt.topology U) Ab.{u + 1}).unit.app
        ((Functor.const U.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) ≫
      (finiteDiscreteSchemeRingIso B U eR).hom.hom).app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).op.obj
          (Opposite.op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
          (proEtTerminal specZ.{u})))) := by
  rw [finiteDiscreteSchemeRingIso_eq, finiteDiscreteSchemeRingIso_eq]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  exact constantScheme_pushforward (AddCommGrpCat.of (ULift.{u + 1} B))
    (Profinite.continuousMapRingObj.{u} B) eR.hom T U j

end

end AlgebraicGeometry.ProEtale.CondensedRing
