/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorComparisons
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRestrictionHomComparison

/-! # Evaluation-normalized internal Hom comparisons

Source: steps 11--12 and the evaluation part of step 13 of the twisted Stacks 00W0 argument.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The local-Hom isomorphisms, normalized solely by preservation of evaluation.
This record asserts neither conjugate action nor naturality.
Source: steps 11--12 and the evaluation part of step 13 of the twisted Stacks 00W0 argument
(blueprint: lem-sf-twisted-action-hom-evaluation-comparisons). -/
structure HomEvaluationComparisons (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) where
  /-- The internal Hom restricts as an isomorphism of sheaves of modules. -/
  hom :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.obj (SheafOfModules.homObj (R := P.coefficient) M N)).obj.a ≅
      SheafOfModules.homObj (R := R) (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a
  /-- Translation's internal Hom comparison. -/
  sigmaHom :
    letI := P.category
    ∀ (M N : Modules R),
      (sigma J s R a).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := R) ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- Translation's Hom comparison is the unique one preserving ordinary evaluation. -/
  sigmaHom_evaluation :
    letI := P.category
    ∀ (M N : Modules R),
      (sigma J s R a).map (evaluationMap M N) =
      (T.sigmaTensor M (SheafOfModules.homObj (R := R) M N)).hom ≫
        tensorMap (𝟙 _) (sigmaHom M N).hom ≫
          evaluationMap ((sigma J s R a).obj M) ((sigma J s R a).obj N)
  /-- Evaluation is the same evaluation of the restricted sheaves. -/
  evaluation :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.map (evaluationMap M N)).hom.f =
      (T.tensor M (SheafOfModules.homObj (R := P.coefficient) M N)).hom ≫
        tensorMap (𝟙 _) (hom M N).hom ≫
          evaluationMap (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a

private theorem untranspose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N Q : Modules S)
    (f : Q ⟶ SheafOfModules.homObj (R := S) M N) :
    (SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f =
      tensorMap (𝟙 M) f ≫ evaluationMap M N := by
  apply (SheafOfModules.tensorHomEquiv (R := S) M Q N).injective
  simp only [Equiv.apply_symm_apply, tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, evaluationMap, Category.comp_id]

private noncomputable def translationHomComparison (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Modules R) :
    (sigma J s R a).obj (SheafOfModules.homObj (R := R) M N) ⟶
      SheafOfModules.homObj (R := R) ((sigma J s R a).obj M) ((sigma J s R a).obj N) :=
  SheafOfModules.tensorHomEquiv (R := R) _ _ _
    ((T.sigmaTensor M (SheafOfModules.homObj (R := R) M N)).inv ≫
      (sigma J s R a).map (evaluationMap M N))

omit [s.functor.IsContinuous J J] in
private theorem translationHomComparison_isIso (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Modules R) :
    IsIso (translationHomComparison J s R a P T M N) := by
  let F := sigma J s R a
  have hF : F.IsEquivalence := by
    change (sigma J s R a).IsEquivalence
    rw [← P.translation_eq]
    infer_instance
  let H := SheafOfModules.homObj (R := R) M N
  let β := translationHomComparison J s R a P T M N
  let ff := Functor.FullyFaithful.ofFullyFaithful F
  have hb (Q : Modules R) : Function.Bijective
      (fun g : F.obj Q ⟶ F.obj H ↦ g ≫ β) := by
    let e : (F.obj Q ⟶ F.obj H) ≃
        (F.obj Q ⟶ SheafOfModules.homObj (R := R) (F.obj M) (F.obj N)) :=
      ff.homEquiv.symm |>.trans
        ((SheafOfModules.tensorHomEquiv (R := R) M Q N).symm.trans
          (ff.homEquiv.trans ((Iso.homCongr (T.sigmaTensor M Q) (Iso.refl _)).trans
            (SheafOfModules.tensorHomEquiv (R := R) (F.obj M) (F.obj Q) (F.obj N)))))
    have he (f : Q ⟶ H) : e (F.map f) = F.map f ≫ β := by
      change e (ff.homEquiv f) = F.map f ≫ β
      dsimp only [e, Equiv.trans_apply]
      rw [ff.homEquiv.symm_apply_apply, untranspose_evaluation]
      change SheafOfModules.tensorHomEquiv (R := R) (F.obj M) (F.obj Q) (F.obj N)
        ((T.sigmaTensor M Q).inv ≫ F.map (tensorMap (𝟙 M) f ≫ evaluationMap M N) ≫
          (Iso.refl (F.obj N)).hom) = _
      rw [Iso.refl_hom, Category.comp_id, F.map_comp]
      have ht : (T.sigmaTensor M Q).inv ≫ F.map (tensorMap (𝟙 M) f) =
          tensorMap (𝟙 (F.obj M)) (F.map f) ≫ (T.sigmaTensor M H).inv := by
        apply (cancel_mono (T.sigmaTensor M H).hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rw [T.sigmaTensor_naturality, F.map_id, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, ht, Category.assoc]
      simpa only [tensorMap, id_tensorHom, translationHomComparison, β] using
        SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := R) (F.obj M) (F.map f)
          ((T.sigmaTensor M H).inv ≫ F.map (evaluationMap M N))
    have he' : (fun g : F.obj Q ⟶ F.obj H ↦ g ≫ β) = e := by
      funext g
      obtain ⟨f, rfl⟩ := ff.homEquiv.surjective g
      exact (he f).symm
    rw [he']
    exact e.bijective
  apply isIso_of_yoneda_map_bijective β
  intro Q
  let e := F.objObjPreimageIso Q
  refine ⟨?_, ?_⟩
  · intro f g h
    apply (cancel_epi e.hom).1
    apply (hb (F.objPreimage Q)).1
    simpa only [Category.assoc] using congrArg (e.hom ≫ ·) h
  · intro f
    obtain ⟨g, hg⟩ := (hb (F.objPreimage Q)).2 (e.hom ≫ f)
    refine ⟨e.inv ≫ g, ?_⟩
    change (e.inv ≫ g) ≫ β = f
    change g ≫ β = e.hom ≫ f at hg
    rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The normalized tensor comparisons admit evaluation-preserving local-Hom comparisons.
Source: steps 11--12 and the evaluation part of step 13 of the twisted Stacks 00W0
argument; Stacks 04TT for local Hom.
(blueprint: lem-sf-twisted-action-hom-evaluation-comparisons).

Proof: on the action-site slice over an object V, normalize a degree-n arrow by
inverse n-th translation. The slice relation forces the degree of every slice morphism,
so the normalization and degree-zero inclusion are mutually inverse equivalences up to
the power isomorphisms. Coverings correspond because the topology is generated by
translated degree-zero covers. Restriction therefore gives an equivalence of module
sheaves on these slices. Full faithfulness identifies all local linear maps between
the restrictions of M and N. These identifications commute with further restriction to
a slice, since both send a local family of linear maps to the same family on that slice.
They are linear over the restricted coefficient ring. Thus they define the sheaf Hom
isomorphism hom. For sigmaHom use the equivalences of slices induced by s.inverse and s,
and transport scalars by a. Again a local linear map goes to its translated local family,
which gives mutually inverse maps of module sheaves.
Evaluation applies a local family to its argument. Under both constructions this gives
the identical section as first evaluating and then restricting or translating. Check on
pure tensors and use the sheafification universal property to obtain both evaluation
equations with the normalized tensor comparisons T. No global equivariance restriction
is imposed on the slice Hom. This applies unchanged to zero modules, the zero ring,
and an empty base site. Naturality and the action formula are deliberately not assumed;
they follow from these evaluation equations by the tensor-Hom adjunction.
-/
theorem homEvaluationComparisons [HasPullbacks C] (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) :
    Nonempty (HomEvaluationComparisons J s R a P T) := by
  let := P.category
  have hr := restrictionHomComparison_isIso J s R a P T
  have ht := translationHomComparison_isIso J s R a P T
  refine ⟨{
    hom := fun M N ↦ asIso (restrictionHomComparison J s R a P T M N)
    sigmaHom := fun M N ↦ asIso (translationHomComparison J s R a P T M N)
    sigmaHom_evaluation := ?_
    evaluation := ?_ }⟩
  · intro M N
    change _ = (T.sigmaTensor M _).hom ≫
      tensorMap (𝟙 _) (translationHomComparison J s R a P T M N) ≫ _
    rw [← untranspose_evaluation]
    simp only [translationHomComparison, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  · intro M N
    change _ = (T.tensor M _).hom ≫
      tensorMap (𝟙 _) (restrictionHomComparison J s R a P T M N) ≫ _
    rw [← untranspose_evaluation]
    simp only [restrictionHomComparison, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

end CategoryTheory.TwistedActionRingedSite
