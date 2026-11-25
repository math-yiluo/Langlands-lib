/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorComparisons
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTranslationHomComparison

/-! # Equivariant currying for twisted-action fixed pairs

Source: Stacks, sites-modules.tex, section-internal-hom, lemma-internal-hom-restriction
and lemma-internal-hom-adjoint-tensor; the formal conjugate-action argument
for steps 11--12 of the twisted action-site construction.
(blueprint: lem-sf-twisted-action-hom-pair-currying).
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
  rw [translationHomComparison]
  exact isIso_translationHomComparison J s R a P T M N

private theorem transpose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N : Modules S) :
    SheafOfModules.tensorHomEquiv (R := S) M _ N (evaluationMap M N) = 𝟙 _ :=
  (SheafOfModules.tensorHomEquiv (R := S) M _ N).apply_symm_apply _

private theorem evaluation_injective
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N T : Modules S)
    (f g : T ⟶ SheafOfModules.homObj (R := S) M N)
    (h : tensorMap (𝟙 M) f ≫ evaluationMap M N =
      tensorMap (𝟙 M) g ≫ evaluationMap M N) : f = g := by
  have hh := congrArg (SheafOfModules.tensorHomEquiv (R := S) M T N) h
  simpa only [tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, transpose_evaluation,
    Category.comp_id] using hh

private theorem evaluation_conjugate
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' T : Modules S}
    (e : M' ≅ M) (g : N ⟶ N') (k : T ⟶ SheafOfModules.homObj (R := S) M' N) :
    tensorMap e.hom (k ≫ SheafOfModules.homObjMap (R := S) e.inv g) ≫
        evaluationMap M N' = tensorMap (𝟙 M') k ≫ evaluationMap M' N ≫ g := by
  have ht : tensorMap e.hom (k ≫ SheafOfModules.homObjMap (R := S) e.inv g) =
      tensorMap e.hom (𝟙 T) ≫
        tensorMap (𝟙 M) (k ≫ SheafOfModules.homObjMap (R := S) e.inv g) := by
    simp only [tensorMap, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [ht]
  simp only [tensorMap, tensorHom_id, id_tensorHom, Category.assoc]
  apply (SheafOfModules.tensorHomEquiv (R := S) M' T N').injective
  rw [SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := S),
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := S), transpose_evaluation, Category.comp_id,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := S),
    SheafOfModules.tensorHomEquiv_comp_homObjMap (R := S), transpose_evaluation, Category.id_comp]
  simp only [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    Iso.hom_inv_id, Category.comp_id]

omit [s.functor.IsContinuous J J] in
private theorem homAction_isIso (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Pairs (sigma J s R a)) :
    IsIso (translationHomComparison J s R a P T M.obj.a N.obj.a ≫
      SheafOfModules.homObjMap (R := R) (pairIso M).inv (pairIso N).hom) := by
  have := translationHomComparison_isIso J s R a P T M.obj.a N.obj.a
  have hi : IsIso (SheafOfModules.homObjMap (R := R) (pairIso M).inv
      (pairIso N).hom) := by
    refine ⟨⟨SheafOfModules.homObjMap (R := R) (pairIso M).hom (pairIso N).inv,
      ?_, ?_⟩⟩
    all_goals simp only [SheafOfModules.homObjMap_comp_homObjMap,
      Iso.hom_inv_id, Iso.inv_hom_id, SheafOfModules.homObjMap_id]
  infer_instance

private noncomputable def homAction (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Pairs (sigma J s R a)) :
    (sigma J s R a).obj (SheafOfModules.homObj (R := R) M.obj.a N.obj.a) ⟶
      SheafOfModules.homObj (R := R) M.obj.a N.obj.a :=
  translationHomComparison J s R a P T M.obj.a N.obj.a ≫
    SheafOfModules.homObjMap (R := R) (pairIso M).inv (pairIso N).hom

omit [s.functor.IsContinuous J J] in
private theorem untranspose_translation (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N Q : Pairs (sigma J s R a))
    (g : Q.obj.a ⟶ SheafOfModules.homObj (R := R) M.obj.a N.obj.a) :
    tensorMap (pairIso M).hom
        ((sigma J s R a).map g ≫ homAction J s R a P T M N) ≫
        evaluationMap M.obj.a N.obj.a =
      (T.sigmaTensor M.obj.a Q.obj.a).inv ≫
        (sigma J s R a).map (tensorMap (𝟙 M.obj.a) g ≫
          evaluationMap M.obj.a N.obj.a) ≫ (pairIso N).hom := by
  let F := sigma J s R a
  let H := SheafOfModules.homObj (R := R) M.obj.a N.obj.a
  change tensorMap (pairIso M).hom
    (F.map g ≫ translationHomComparison J s R a P T M.obj.a N.obj.a ≫
      SheafOfModules.homObjMap (R := R) (pairIso M).inv (pairIso N).hom) ≫ _ = _
  rw [← Category.assoc (F.map g), evaluation_conjugate]
  have ht := T.sigmaTensor_naturality (𝟙 M.obj.a) g
  simp only [Functor.map_id] at ht
  have ht' : tensorMap (𝟙 (F.obj M.obj.a)) (F.map g) ≫
      (T.sigmaTensor M.obj.a H).inv =
      (T.sigmaTensor M.obj.a Q.obj.a).inv ≫ F.map (tensorMap (𝟙 M.obj.a) g) := by
    apply (cancel_mono (T.sigmaTensor M.obj.a H).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using
      congrArg ((T.sigmaTensor M.obj.a Q.obj.a).inv ≫ ·) ht.symm
  have hu : tensorMap (𝟙 (F.obj M.obj.a))
      (translationHomComparison J s R a P T M.obj.a N.obj.a) ≫
        evaluationMap (F.obj M.obj.a) (F.obj N.obj.a) =
      (T.sigmaTensor M.obj.a H).inv ≫ F.map (evaluationMap M.obj.a N.obj.a) := by
    rw [← untranspose_evaluation, translationHomComparison]
    exact (SheafOfModules.tensorHomEquiv (R := R) _ _ _).symm_apply_apply _
  calc
    _ = tensorMap (𝟙 (F.obj M.obj.a)) (F.map g) ≫
        (tensorMap (𝟙 (F.obj M.obj.a))
          (translationHomComparison J s R a P T M.obj.a N.obj.a) ≫
            evaluationMap (F.obj M.obj.a) (F.obj N.obj.a)) ≫ (pairIso N).hom := by
      simp only [F, tensorMap, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp]
    _ = tensorMap (𝟙 (F.obj M.obj.a)) (F.map g) ≫
        (T.sigmaTensor M.obj.a H).inv ≫ F.map (evaluationMap M.obj.a N.obj.a) ≫
          (pairIso N).hom := by rw [hu]; simp only [Category.assoc]
    _ = _ := by
      rw [← Category.assoc, ht']
      simp only [F, Category.assoc, Functor.map_comp]

omit [s.functor.IsContinuous J J] in
private theorem pairIso_hom (M : Pairs (sigma J s R a)) :
    (pairIso M).hom = M.obj.str := rfl

omit [s.functor.IsContinuous J J] in
private theorem curry_equivariant (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N Q : Pairs (sigma J s R a))
    (g : Q.obj.a ⟶ SheafOfModules.homObj (R := R) M.obj.a N.obj.a) :
    (sigma J s R a).map g ≫ homAction J s R a P T M N = Q.obj.str ≫ g ↔
      (sigma J s R a).map (tensorMap (𝟙 M.obj.a) g ≫
          evaluationMap M.obj.a N.obj.a) ≫ N.obj.str =
        (T.sigmaTensor M.obj.a Q.obj.a).hom ≫ tensorMap M.obj.str Q.obj.str ≫
          tensorMap (𝟙 M.obj.a) g ≫ evaluationMap M.obj.a N.obj.a := by
  have he : tensorMap (pairIso M).hom (Q.obj.str ≫ g) ≫
      evaluationMap M.obj.a N.obj.a =
      tensorMap M.obj.str Q.obj.str ≫ tensorMap (𝟙 M.obj.a) g ≫
        evaluationMap M.obj.a N.obj.a := by
    simp only [pairIso_hom, tensorMap, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.comp_id]
  constructor
  · intro h
    have hh := untranspose_translation J s R a P T M N Q g
    rw [h, he] at hh
    have hh' := congrArg ((T.sigmaTensor M.obj.a Q.obj.a).hom ≫ ·) hh.symm
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, pairIso_hom] using hh'
  · intro h
    apply evaluation_injective M.obj.a N.obj.a _
    apply (cancel_epi (tensorMap (pairIso M).hom
      (𝟙 ((sigma J s R a).obj Q.obj.a)))).1
    have hh := untranspose_translation J s R a P T M N Q g
    rw [pairIso_hom J s R a N, h, Iso.inv_hom_id_assoc, ← he] at hh
    simpa only [tensorMap, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id] using hh

omit [s.functor.IsContinuous J J] in
/-- The canonical conjugate Hom action is invertible, and currying preserves equivariance.
Source: Stacks, sites-modules.tex, lemma-internal-hom-adjoint-tensor; formal
conjugate-action calculation in steps 11--12 of the twisted action construction.
(blueprint: lem-sf-twisted-action-hom-pair-currying).

Proof: translation is an equivalence. Its natural tensor comparison and the
ordinary tensor-Hom adjunction identify postcomposition with the transpose of
translated evaluation with a bijection on Hom sets. Essential surjectivity and
Yoneda therefore make this transpose invertible. Composing it with Hom of the
inverse source action and the target action gives the displayed invertible
conjugate action. Naturality of the tensor comparison rewrites its evaluation
as translated evaluation followed by the target action. A map commutes with
the conjugate action exactly when its untranspose commutes with the diagonal
tensor action: apply evaluation, cancel the invertible source action and tensor
comparison, and use injectivity of the tensor-Hom adjunction. This includes
zero modules, the zero ring, and empty sites without additional hypotheses. -/
theorem homPair_currying (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Pairs (sigma J s R a)) :
    let h :=
      (SheafOfModules.tensorHomEquiv (R := R) _ _ _
        ((T.sigmaTensor M.obj.a
          (SheafOfModules.homObj (R := R) M.obj.a N.obj.a)).inv ≫
            (sigma J s R a).map (evaluationMap M.obj.a N.obj.a))) ≫
          SheafOfModules.homObjMap (R := R) (pairIso M).inv (pairIso N).hom
    IsIso h ∧ ∀ (Q : Pairs (sigma J s R a))
      (g : Q.obj.a ⟶ SheafOfModules.homObj (R := R) M.obj.a N.obj.a),
      (sigma J s R a).map g ≫ h = Q.obj.str ≫ g ↔
        (sigma J s R a).map (tensorMap (𝟙 M.obj.a) g ≫
            evaluationMap M.obj.a N.obj.a) ≫ N.obj.str =
          (T.sigmaTensor M.obj.a Q.obj.a).hom ≫ tensorMap M.obj.str Q.obj.str ≫
            tensorMap (𝟙 M.obj.a) g ≫ evaluationMap M.obj.a N.obj.a := by
  constructor
  · simpa only [translationHomComparison] using homAction_isIso J s R a P T M N
  · intro Q g
    simpa only [homAction, translationHomComparison] using
      curry_equivariant J s R a P T M N Q g

end CategoryTheory.TwistedActionRingedSite
