/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct

/-! # Quotient normalization determines the ordinary coefficient tensor square -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

section ConstantMonoidal
variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

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

private instance constantPresheafAdj_monoidal : (constantPresheafAdj A hT).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance constantSheafAdj_monoidal : (constantSheafAdj J A hT).IsMonoidal := by
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

private noncomputable def precomposeEvaluationIso (T : C) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅
      (evaluation Dᵒᵖ A).obj (op (F.obj T)) := Iso.refl _

private instance precomposeEvaluation_monoidal (T : C) : NatTrans.IsMonoidal
    (precomposeEvaluationIso (A := A) F T).hom where
  unit := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.ε]
  tensor P Q := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.μ]

private instance sheafSectionsNatIsoEvaluation_monoidal {T : C} : NatTrans.IsMonoidal
    (sheafSectionsNatIsoEvaluation J A (X := T)).hom := by
  change NatTrans.IsMonoidal (𝟙 (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)))
  infer_instance

private noncomputable def pushforwardSectionsIso (T : C) :
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

private instance pushforwardSections_monoidal (T : C) : NatTrans.IsMonoidal
    (pushforwardSectionsIso (A := A) F J K T).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

omit [MonoidalCategory A] [BraidedCategory A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
private theorem pushforwardUnderlying_inv_app (P : Sheaf K A) :
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).inv.app P = 𝟙 _ := by
  have h :=
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom_inv_id_app P
  rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    Category.id_comp] at h
  exact h

end Pullback

section SectionMaps
variable {C B : Type*} [Category C] [Category B] [MonoidalCategory B]
    (J : GrothendieckTopology C) [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
attribute [local instance] Sheaf.monoidalCategory

end SectionMaps

end ConstantMonoidal

private theorem coefficientQuotient_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : ModuleCat.{u + 1} A) :
    Epi (supportedCoefficientQuotient A i M) := by
  constructor
  intro F a b hab
  let adj := supportedCoefficientAdjunction A i
  apply (adj.homEquiv M F).injective
  have : Mono ((supportedEtaleSectionsι A X i.openComplement).app F) := by
    dsimp [supportedEtaleSectionsι]
    infer_instance
  apply (cancel_mono ((supportedEtaleSectionsι A X i.openComplement).app F)).1
  apply ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm.injective
  have ha := (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F
    ((adj.homEquiv M F) a)
  have hb := (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F
    ((adj.homEquiv M F) b)
  erw [Equiv.symm_apply_apply] at ha hb
  exact ha.symm.trans (hab.trans hb)

end AlgebraicGeometry.Etale
