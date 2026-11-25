/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Pulling the constant coefficient ring to a scheme

Source: the monoidal adjunctions defining inverse image and Section 5.3 of
Bhatt--Scholze. The constant-sheaf adjunction and terminal sections identify
constant sheaves before and after inverse image, including multiplication. -/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite MonoidalCategory

private instance evaluationMonoidal {C A : Type*} [Category C] [Category A]
    [MonoidalCategory A] (U : C) : ((evaluation C A).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

section
variable {C A : Type*} [Category C] [Category A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  {T : C} (hT : IsTerminal T)
attribute [local instance] Sheaf.monoidalCategory

private noncomputable instance sectionsMonoidal : ((sheafSections J A).obj (op T)).LaxMonoidal :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)).LaxMonoidal

private instance finiteDiscreteSchemeRingInst1 : (constantPresheafAdj A hT).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance finiteDiscreteSchemeRingInst2 : (constantSheafAdj J A hT).IsMonoidal := by
  unfold constantSheafAdj
  infer_instance
end

section Pullback
variable {C D A : Type*} [Category C] [Category D] [Category A]
  [MonoidalCategory A] [BraidedCategory A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [F.IsContinuous J K]
attribute [local instance] Sheaf.monoidalCategory

noncomputable def precomposeEvaluationIso (T : C) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅
      (evaluation Dᵒᵖ A).obj (op (F.obj T)) := Iso.refl _

private instance finiteDiscreteSchemeRingInst3 (T : C) : NatTrans.IsMonoidal
    (precomposeEvaluationIso (A := A) F T).hom where
  unit := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.ε]
  tensor P Q := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.μ]

private instance finiteDiscreteSchemeRingInst4 {T : C} : NatTrans.IsMonoidal
    (sheafSectionsNatIsoEvaluation J A (X := T)).hom := by
  change NatTrans.IsMonoidal (𝟙 (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)))
  infer_instance

noncomputable def pushforwardSectionsIso (T : C) :
    F.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op (F.obj T)) :=
  Functor.isoWhiskerLeft _ (sheafSectionsNatIsoEvaluation J A) ≪≫
    (Functor.associator (F.sheafPushforwardContinuous A J K)
      (sheafToPresheaf J A) ((evaluation Cᵒᵖ A).obj (op T))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F A J K).symm ((evaluation Cᵒᵖ A).obj (op T)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precomposeEvaluationIso F T) ≪≫
    (sheafSectionsNatIsoEvaluation K A).symm

private instance finiteDiscreteSchemeRingInst5 (T : C) : NatTrans.IsMonoidal
    (pushforwardSectionsIso (A := A) F J K T).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

variable [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]
  [(Functor.sheafPullbackConstruction.sheafPullback F A J K).Monoidal]

local instance finiteDiscreteSchemeRingInst6
    : (Functor.sheafPullbackConstruction.sheafPullback F A J K).OplaxMonoidal :=
  Functor.Monoidal.toOplaxMonoidal

variable [(Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).IsMonoidal]

noncomputable def constantPullbackMonoidalIso {T : C} (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) :
    constantSheaf K A ≅ constantSheaf J A ⋙
      Functor.sheafPullbackConstruction.sheafPullback F A J K :=
  (conjugateIsoEquiv
    ((constantSheafAdj J A hT).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K))
    (constantSheafAdj K A hFT)).symm (pushforwardSectionsIso (A := A) F J K T)

instance finiteDiscreteSchemeRingInst7 {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T)) :
    NatTrans.IsMonoidal (constantPullbackMonoidalIso (A := A) F J K hT hFT).hom := by
  have h1 : (constantSheafAdj J A hT).IsMonoidal := inferInstance
  have h2 : (constantSheafAdj K A hFT).IsMonoidal := inferInstance
  have h3 : (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).IsMonoidal :=
    inferInstance
  have h4 := Adjunction.isMonoidal_comp (constantSheafAdj J A hT)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K)
  let := h4
  exact isMonoidal_conjugateEquiv_symm
    ((constantSheafAdj J A hT).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K))
    (constantSheafAdj K A hFT) (pushforwardSectionsIso (A := A) F J K T).hom
end Pullback

section ConstantRing
attribute [local instance] Sheaf.monoidalCategory

private theorem constantRingMonObj {C : Type*} [Category C] (B : Type*) [CommRing B] :
    (Functor.const C).monObjObj (AddCommGrpCat.of B) =
      Functor.monObjCompForget₂ ((Functor.const C).obj (RingCat.of B)) := by
  apply MonObj.ext
  ext U
  rfl

private theorem constantSheafRingMonObj {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J Ab.{w}]
    [(J.W (A := Ab.{w})).IsMonoidal] (B : Type w) [CommRing B] :
    (constantSheaf J Ab.{w}).monObjObj (AddCommGrpCat.of B) =
      Sheaf.monObj_presheafToSheaf_obj J
        (((Functor.const Cᵒᵖ).obj (RingCat.of B)) ⋙ forget₂ RingCat Ab) := by
  have h := Functor.monObjObj_comp (Functor.const Cᵒᵖ) (presheafToSheaf J Ab.{w})
    (AddCommGrpCat.of B)
  refine h.trans ?_
  let transfer (m : MonObj ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of B))) :
      MonObj ((constantSheaf J Ab.{w}).obj (AddCommGrpCat.of B)) :=
    @Functor.monObjObj _ _ _ _ _ _ (presheafToSheaf J Ab.{w}) _ _ m
  exact congrArg transfer (constantRingMonObj (C := Cᵒᵖ) B)

end ConstantRing

private theorem monHomInvExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N : C} (mM : MonObj M) (mN : MonObj N) (e : M ≅ N)
    (h : @IsMonHom _ _ _ M N mM mN e.hom) :
    @IsMonHom _ _ _ N M mN mM e.inv := by
  let := mM
  let := mN
  let := h
  infer_instance

private theorem monHomCompExplicit {C : Type*} [Category C] [MonoidalCategory C]
    {M N O : C} (mM : MonObj M) (mN : MonObj N) (mO : MonObj O)
    (f : M ⟶ N) (g : N ⟶ O)
    (hf : @IsMonHom _ _ _ M N mM mN f)
    (hg : @IsMonHom _ _ _ N O mN mO g) :
    @IsMonHom _ _ _ M O mM mO (f ≫ g) := by
  let := mM
  let := mN
  let := mO
  let := hf
  let := hg
  infer_instance

namespace AlgebraicGeometry.ProEtale
open Scheme

noncomputable def constantPointIso :
    constantSheaf (ProEt.topology specZ.{u}) Ab.{u + 1} ≅
      constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ pointUpperStar :=
  constantPullbackMonoidalIso profiniteToProEt (coherentTopology Profinite.{u})
    (ProEt.topology specZ.{u}) (terminalIsTerminal (C := Profinite.{u}))
    ((terminalIsTerminal (C := Profinite.{u})).isTerminalObj profiniteToProEt)

instance finiteDiscreteSchemeRingInst8 : NatTrans.IsMonoidal constantPointIso.{u}.hom := by
  unfold constantPointIso
  infer_instance

/-- The identity object is an explicit terminal pro-etale object.
The equality condition determines the witness uniquely. -/
theorem proEtTerminal_exists (T : Scheme.{u}) :
    ∃ W : T.ProEt, W = MorphismProperty.Over.mk ⊤ (𝟙 T) (by infer_instance) :=
  ⟨_, rfl⟩

/-- A terminal object, kept behind its equality API to avoid reducing iterated pullbacks
of the identity scheme during kernel checks of section comparisons. The defining theorem
specifies the exact identity object, so this choice carries no arbitrary data. -/
noncomputable def proEtTerminal (T : Scheme.{u}) : T.ProEt :=
  Classical.choose (proEtTerminal_exists T)

/-- The terminal object is exactly the identity scheme over itself. -/
theorem proEtTerminal_eq (T : Scheme.{u}) :
    proEtTerminal T = MorphismProperty.Over.mk ⊤ (𝟙 T) (by infer_instance) :=
  Classical.choose_spec (proEtTerminal_exists T)

instance finiteDiscreteSchemeRingInst9 (T : Scheme.{u}) : IsIso (proEtTerminal T).hom := by
  rw [proEtTerminal_eq]
  change IsIso (𝟙 T)
  infer_instance

instance finiteDiscreteSchemeRingInst10 (T : Scheme.{u}) : IsIso
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
      (proEtTerminal specZ.{u})).hom := by
  rw [proEtTerminal_eq]
  change IsIso (pullback.snd (𝟙 specZ.{u}) (toSpecZ T))
  infer_instance

noncomputable def proEtIsTerminal {T : Scheme.{u}} (U : T.ProEt) [IsIso U.hom] : IsTerminal U :=
  IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk (V.hom ≫ inv U.hom) (by simp) trivial)
    (by
      intro V m
      apply MorphismProperty.Comma.Hom.ext
      · apply (cancel_mono U.hom).mp
        simp
      · exact Subsingleton.elim _ _)

noncomputable def constantSchemeIso (T : Scheme.{u}) :
    constantSheaf (ProEt.topology T) Ab.{u + 1} ≅
      constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙ upperStarFromPoint T :=
  constantPullbackMonoidalIso
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T))
    (ProEt.topology specZ.{u}) (ProEt.topology T)
    (proEtIsTerminal (proEtTerminal specZ.{u}))
    (proEtIsTerminal
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ T)).obj
        (proEtTerminal specZ.{u}))) ≪≫
  Functor.isoWhiskerRight constantPointIso ((toSpecZ T)^*[Ab.{u + 1}]) ≪≫
  Functor.associator _ _ _

instance finiteDiscreteSchemeRingInst11
    (T : Scheme.{u}) : NatTrans.IsMonoidal (constantSchemeIso T).hom := by
  dsimp only [constantSchemeIso, Iso.trans_hom, Functor.isoWhiskerRight_hom]
  infer_instance
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme
open scoped CategoryTheory.Obj

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

theorem finiteDiscreteSchemeRingIso_exists (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    ∃ e : (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T), e =
      (constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} B)) ≪≫
    (upperStarFromPoint T).mapIso eR :=
  ⟨_, rfl⟩

/-- The explicit constant coefficient comparison, accessed through its equality API.
This construction chooses the unique value specified by a proved equality, so it adds
no arbitrary coefficient identification. -/
noncomputable def finiteDiscreteSchemeRingIso (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T :=
  Classical.choose (finiteDiscreteSchemeRingIso_exists B T eR)

theorem finiteDiscreteSchemeRingIso_eq (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B) :
    finiteDiscreteSchemeRingIso B T eR =
      (constantSchemeIso T).app (AddCommGrpCat.of (ULift.{u + 1} B)) ≪≫
    (upperStarFromPoint T).mapIso eR :=
  Classical.choose_spec (finiteDiscreteSchemeRingIso_exists B T eR)

instance finiteDiscreteSchemeRingInst12 (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    [IsMonHom eR.hom] : IsMonHom (finiteDiscreteSchemeRingIso B T eR).hom := by
  let A := AddCommGrpCat.of (ULift.{u + 1} B)
  let S := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let P := upperStarFromPoint T
  let Q := constantSheaf (ProEt.topology T) Ab.{u + 1}
  let transfer (m : MonObj (S.obj A)) : MonObj (P.obj (S.obj A)) :=
    @Functor.monObjObj _ _ _ _ _ _ P _ _ m
  have hS := constantSheafRingMonObj (coherentTopology Profinite.{u}) (ULift.{u + 1} B)
  have hQ := constantSheafRingMonObj (ProEt.topology T) (ULift.{u + 1} B)
  let mS := Sheaf.monObj_presheafToSheaf_obj (coherentTopology Profinite.{u})
    (((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  let mQ := Sheaf.monObj_presheafToSheaf_obj (ProEt.topology T)
    (((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ⋙
      forget₂ RingCat Ab)
  have hi : @IsMonHom _ _ _ (P.obj (S.obj A)) (Q.obj A)
      (transfer mS) mQ ((constantSchemeIso T).inv.app A) :=
    IsMonHom.of_eq
      (h₁ := transfer (S.monObjObj A)) (h₂ := Q.monObjObj A)
      ((constantSchemeIso T).inv.app A) (congrArg transfer hS) hQ
      (hf := Functor.isMonHom_compAlgHom S P (constantSchemeIso T).inv A)
  have hh := monHomInvExplicit (transfer mS) mQ ((constantSchemeIso T).app A).symm hi
  have hmap : IsMonHom (P.map eR.hom) := inferInstance
  rw [finiteDiscreteSchemeRingIso_eq]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  exact monHomCompExplicit mQ (transfer mS) _
    ((constantSchemeIso T).hom.app A) (P.map eR.hom) hh hmap
end AlgebraicGeometry.ProEtale
