/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing

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

private instance : (constantPresheafAdj A hT).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance : (constantSheafAdj J A hT).IsMonoidal := by
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

private instance (T : C) : NatTrans.IsMonoidal
    (precomposeEvaluationIso (A := A) F T).hom where
  unit := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.ε]
  tensor P Q := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.μ]

private instance {T : C} : NatTrans.IsMonoidal
    (sheafSectionsNatIsoEvaluation J A (X := T)).hom := by
  change NatTrans.IsMonoidal (𝟙 (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)))
  infer_instance

private instance (T : C) : NatTrans.IsMonoidal
    (pushforwardSectionsIso (A := A) F J K T).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

variable [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]
  [(Functor.sheafPullbackConstruction.sheafPullback F A J K).Monoidal]

local instance : (Functor.sheafPullbackConstruction.sheafPullback F A J K).OplaxMonoidal :=
  Functor.Monoidal.toOplaxMonoidal

variable [(Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F A J K).IsMonoidal]

instance {T : C} (hT : IsTerminal T) (hFT : IsTerminal (F.obj T)) :
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

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open Scheme
open scoped CategoryTheory.Obj

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- The monoidal constant-ring identification on a profinite point pulls to every scheme.
Source: Bhatt--Scholze, Section 5.3; formal uniqueness of monoidal left adjoints
(blueprint: lem-weil-pbc-finite-discrete-scheme-ring-constant).

Proof. The constant-sheaf functor is left adjoint to sections at a terminal object.
Pushforward preserves these sections, since base change sends the terminal pro-etale
object to a terminal object. Conjugate this monoidal sections comparison to obtain
the monoidal constant-sheaf pullback comparison, first from profinite sets to Spec Z,
then from Spec Z to T. Apply it to the ring object ULift B. The composite-functor
monoid structure agrees with successive transport by monObjObj_comp; the constant
presheaf ring structure agrees with the pointwise transported one. Finally map the
given point ring isomorphism along upperStarFromPoint. Every map preserves the
unit and multiplication, including for empty schemes and the zero ring. -/
theorem finiteDiscreteSchemeRing_constant (T : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
    (heR : IsMonHom eR.hom) :
    ∃ e : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        condensedRingObj (Profinite.continuousMapRingObj.{u} B) T,
      IsMonHom e.hom := by
  let := heR
  exact ⟨finiteDiscreteSchemeRingIso B T eR, inferInstance⟩

end AlgebraicGeometry.ProEtale
