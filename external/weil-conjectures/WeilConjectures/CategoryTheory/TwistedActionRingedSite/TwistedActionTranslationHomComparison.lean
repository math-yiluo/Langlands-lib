/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorComparisons

/-! # Canonical Hom comparison for translation

Source: Stacks, sites-modules.tex, section-internal-hom, lemma-internal-hom-restriction
and lemma-internal-hom-adjoint-tensor; the formal conjugate-action argument
for steps 11--12 of the twisted action-site construction.
(blueprint: lem-sf-twisted-action-translation-hom-comparison).
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

private theorem untranspose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N Q : Modules S)
    (f : Q ⟶ SheafOfModules.homObj (R := S) M N) :
    (SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f =
      tensorMap (𝟙 M) f ≫ evaluationMap M N := by
  apply (SheafOfModules.tensorHomEquiv (R := S) M Q N).injective
  simp only [Equiv.apply_symm_apply, tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, evaluationMap, Category.comp_id]

@[irreducible]
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

omit [s.functor.IsContinuous J J] in
/-- The transpose of inverse tensor comparison followed by translated evaluation is invertible.
Source: Stacks, sites-modules.tex, lemma-internal-hom-adjoint-tensor;
formal tensor-Hom argument for a tensor autoequivalence.
(blueprint: lem-sf-twisted-action-translation-hom-comparison).

Proof: on test objects FQ, full faithfulness identifies maps into F Hom(M,N)
with maps Q to Hom(M,N). Untranspose, apply F, precompose with the inverse
tensor comparison and transpose again. This is a composite of equivalences.
Tensor naturality identifies it with postcomposition by the displayed map.
Essential surjectivity extends this bijectivity to every test object, and the
Yoneda isomorphism criterion finishes. Only naturality of sigmaTensor and the
translation equivalence are used; zero objects and empty sites cause no exception. -/
theorem isIso_translationHomComparison (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Modules R) :
    IsIso (SheafOfModules.tensorHomEquiv (R := R) _ _ _
      ((T.sigmaTensor M (SheafOfModules.homObj (R := R) M N)).inv ≫
        (sigma J s R a).map (evaluationMap M N))) := by
  simpa only [translationHomComparison] using
    translationHomComparison_isIso J s R a P T M N

end CategoryTheory.TwistedActionRingedSite
