/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
public import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.SignedLineModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SignedLineSheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

/-! # Exactness of coefficient-identified pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.SignedLineDerivedBaseChange

universe r
private theorem ringSheafification {E : Type u} [Category.{v} E]
    [EssentiallySmall.{r} E] (H : GrothendieckTopology E) :
    HasSheafify H RingCat.{r} ∧
      H.PreservesSheafification (CategoryTheory.forget RingCat.{r}) ∧
      H.PreservesSheafification (CategoryTheory.forget AddCommGrpCat.{r}) := by
  have : HasSheafify ((equivSmallModel.{r} E).inverse.inducedTopology H)
      RingCat.{r} := inferInstance
  have : ∀ X : Eᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{r} E).inverse.op) RingCat.{r} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : ∀ X : Eᵒᵖ, HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{r} E).inverse.op) (Type r) :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall _ _
  have : ((equivSmallModel.{r} E).inverse.inducedTopology H).PreservesSheafification
      (CategoryTheory.forget RingCat.{r}) := inferInstance
  have : ((equivSmallModel.{r} E).inverse.inducedTopology H).PreservesSheafification
      (CategoryTheory.forget AddCommGrpCat.{r}) := inferInstance
  exact ⟨hasSheafifyEssentiallySmallSite H RingCat.{r}, inferInstance, inferInstance⟩

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

variable
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : KFlatFixedTensor.Modules R) (Q : KFlatFixedTensor.Modules S)
  (t : (pull a).obj P ≅ Q)

/-- Pullback with invertible structural ring map preserves finite limits.
Source: Stacks Project, Tags 00X6, 03DA, 03DB and 03EL; step 1 of the
Powers and duals argument.
(blueprint: lem-pur-identified-ring-pullback-finite-limits)
Proof: construct the left exact abelian inverse image using filtered comma
categories and left exact sheafification. The invertible adjunct of a identifies
its transported ring with S. Transport scalar multiplication through the
set inverse-image product comparisons. Unit tests establish the module laws
and semilinear restrictions on the actual abelian inverse image. The resulting
module adjunction identifies this construction with the specified module pullback,
including its adjunction unit.
The forgetful module functors preserve and reflect finite limits, so the underlying
left exact comparison proves the assertion. No nonzero-ring or point hypothesis
is used, and the argument includes the empty site. -/
theorem identified_ring_pullback_presentations
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (_hcover : CoverPreserving J K U)
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (_ha : IsIso ((rAdj.homEquiv _ _).symm a)) :
    ∃ pr : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation
      (F := U) ((sheafCompose J (CategoryTheory.forget CommRingCat)).obj R)
        ((sheafCompose K (CategoryTheory.forget CommRingCat)).obj S),
      pr.unit = (sheafCompose J (CategoryTheory.forget RingCat)).map a ∧
      ∃ e : pull a ⋙ toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S) ≅
        toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
          Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{max u v w} J K,
        (∀ M : KFlatFixedTensor.Modules R,
          (toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).map
            ((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a
              (module_pushforward_isRightAdjoint_of_universes a)).unit.app M) ≫
              (U.sheafPushforwardContinuous AddCommGrpCat.{max u v w} J K).map
                (e.hom.app M) =
              (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
                AddCommGrpCat.{max u v w} J K).unit.app
                  ((toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj M)) ∧
        ∃ em : pull a ⋙ toSheaf _ ⋙ sheafCompose K
            (CategoryTheory.forget AddCommGrpCat.{max u v w}) ≅
          (toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v w})) ⋙
            Functor.sheafPullbackConstruction.sheafPullback U (Type (max u v w)) J K,
          ∀ (M : KFlatFixedTensor.Modules R) (V : Cᵒᵖ) (x : M.val.obj V),
            (em.hom.app M).hom.app (U.op.obj V)
              (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
                M V.unop x) =
              ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U
                (Type (max u v w)) J K).unit.app
                  ((toSheaf _ ⋙ sheafCompose J
                    (CategoryTheory.forget AddCommGrpCat.{max u v w})).obj M)).hom.app V x := by
  let hmod := module_pushforward_isRightAdjoint_of_universes a
  let := hmod
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : AB5OfSize.{v, max u v} (Type (max u v w)) := AB5OfSize_shrink.{v, max u v, max u v w,
    max u v w} _
  have : AB5OfSize.{v, max u v} AddCommGrpCat.{max u v w} := AB5OfSize_shrink.{v, max u v, max
    u v w, max u v w} _
  let : HasSheafify J (Type (max u v w)) :=
    hasSheafifyEssentiallySmallSite.{v, max u v w, u, (max u v w) + 1, max u v w} J (Type (max
      u v w))
  let : HasSheafify K (Type (max u v w)) :=
    hasSheafifyEssentiallySmallSite.{v, max u v w, u, (max u v w) + 1, max u v w} K (Type (max
      u v w))
  obtain ⟨hJ, _⟩ := coefficientSheafification.{u, v, max u v w} J
  obtain ⟨hK, _⟩ := coefficientSheafification.{u, v, max u v w} K
  let := hJ
  let := hK
  obtain ⟨hRing, hRF, hAF⟩ := ringSheafification.{u, v, max u v w} K
  let := hRing
  let := hRF
  let := hAF
  have : PreservesFilteredColimitsOfSize.{v, max u v}
      (CategoryTheory.forget AddCommGrpCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  have : PreservesFilteredColimitsOfSize.{v, max u v}
      (CategoryTheory.forget RingCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max u v w, max u v w} _
  have : ∀ V : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow U.op V)
      RingCat.{max u v w} := fun _ ↦ hasColimitsOfShape_of_essentiallySmall.{max u v w} _ _
  have : ∀ V : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow U.op V)
      (CategoryTheory.forget RingCat.{max u v w}) := fun _ ↦ inferInstance
  have : ∀ V : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow U.op V)
      (CategoryTheory.forget AddCommGrpCat.{max u v w}) := fun _ ↦ inferInstance
  let adjR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U RingCat.{max u v w} J K
  let A := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let B := (sheafCompose K (forget₂ CommRingCat RingCat)).obj S
  let q := adjR.leftAdjointUniq rAdj
  let b : (Functor.sheafPullbackConstruction.sheafPullback U RingCat J K).obj A ≅ B := q.app A
    ≪≫ asIso ((rAdj.homEquiv _ _).symm a)
  have hb : adjR.unit.app A ≫ (U.sheafPushforwardContinuous RingCat J K).map b.hom = a := by
    dsimp only [b, Iso.trans_hom, Iso.app_hom]
    rw [Functor.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    exact (rAdj.homEquiv _ _).apply_symm_apply a
  let er := (CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso
    J K U (CategoryTheory.forget RingCat.{max u v w})).app A
  let pr : CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation
      (F := U) ((sheafCompose J (CategoryTheory.forget RingCat)).obj A)
        ((sheafCompose K (CategoryTheory.forget RingCat)).obj B) :=
    { unit := (sheafCompose J (CategoryTheory.forget RingCat)).map a
      iso := (sheafCompose K (CategoryTheory.forget RingCat)).mapIso b.symm ≪≫ er
      equation := by
        intro V x
        have h := CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso_unit
          J K U (CategoryTheory.forget RingCat.{max u v w}) A
        have hb' := congrArg (fun f ↦ f.hom.app V x) hb
        have hx := congrArg (fun f ↦ f.hom.app V x) h
        dsimp only [Functor.map_comp] at hx
        dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
        change er.hom.hom.app (U.op.obj V) (b.inv.hom.app (U.op.obj V)
          (a.hom.app V x)) = _
        have hb'' : b.hom.hom.app (U.op.obj V)
            ((adjR.unit.app A).hom.app V x) = a.hom.app V x := hb'
        apply Eq.trans (congrArg (fun y ↦ er.hom.hom.app (U.op.obj V)
          (b.inv.hom.app (U.op.obj V) y)) hb''.symm)
        have hi := ConcreteCategory.congr_hom
          (congrArg (fun f ↦ f.hom.app (U.op.obj V)) b.hom_inv_id)
            ((adjR.unit.app A).hom.app V x)
        exact (congrArg (er.hom.hom.app (U.op.obj V)) hi).trans hx }
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback U (Type (max u v w)) J K) :=
    inferInstance
  obtain ⟨e, he⟩ := SignedLinePullbackConstruction.inverseImage_underlying_of_ring_presentation
    a pr rfl
  let ea := CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso
    J K U (CategoryTheory.forget AddCommGrpCat.{max u v w})
  let em := Functor.isoWhiskerRight e (sheafCompose K (CategoryTheory.forget AddCommGrpCat)) ≪≫
    Functor.isoWhiskerLeft (toSheaf A) ea
  refine ⟨pr, rfl, e, he, em, ?_⟩
  intro M V x
  have h := congrArg (fun f ↦ f.hom.app V x) (he M)
  change (e.hom.app M).hom.app (U.op.obj V)
    (ringedSitePullbackSection a (module_pushforward_isRightAdjoint_of_universes a)
      M V.unop x) = _ at h
  change (ea.hom.app ((toSheaf A).obj M)).hom.app (U.op.obj V)
    ((e.hom.app M).hom.app (U.op.obj V) _) = _
  rw [h]
  exact congrArg (fun f ↦ f.hom.app V x)
    (CategoryTheory.SignedLinePullbackConstruction.sheafPullbackForgetIso_unit
      J K U (CategoryTheory.forget AddCommGrpCat.{max u v w}) ((toSheaf A).obj M))

/-- Coefficient-identified module pullback preserves finite limits.
Source: Stacks Project, Tags 03D2 and 03D3.
(blueprint: lem-pur-identified-ring-pullback-finite-limits)
Proof: use the unit-preserving abelian inverse-image presentation. The abelian
inverse image preserves finite limits, while the module forgetful functor reflects them. -/
theorem identified_ring_pullback_finiteLimits
    [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
    (hcover : CoverPreserving J K U)
    (rInv : Sheaf J RingCat.{max u v w} ⥤ Sheaf K RingCat.{max u v w})
    (rAdj : rInv ⊣ U.sheafPushforwardContinuous RingCat J K)
    (ha : IsIso ((rAdj.homEquiv _ _).symm a)) :
    PreservesFiniteLimits (pull a) := by
  obtain ⟨pr, hr, e, he, em, hem⟩ := identified_ring_pullback_presentations a hcover rInv rAdj ha
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : AB5OfSize.{v, max u v} AddCommGrpCat.{max u v w} :=
    AB5OfSize_shrink.{v, max u v, max u v w, max u v w} _
  obtain ⟨hK, _⟩ := coefficientSheafification.{u, v, max u v w} K
  let := hK
  have : PreservesFiniteLimits (pull a ⋙
      toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves (pull a)
    (toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

end SheafOfModules.SignedLineDerivedBaseChange
