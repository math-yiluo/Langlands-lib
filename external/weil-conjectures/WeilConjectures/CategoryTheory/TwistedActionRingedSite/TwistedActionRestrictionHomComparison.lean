/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorComparisons
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionHomPairCurrying
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionTensorHomNaturality

/-! # The canonical restriction comparison for sheaf Hom

Source: Stacks, sites-modules.tex, section-internal-hom, lemma-internal-hom-restriction
and lemma-internal-hom-adjoint-tensor; the restriction part of steps 11--12 of the
agent-formulated twisted action-site construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [hs : s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

@[reducible] private noncomputable def underlyingRestriction (P : RestrictionPresentation J s R a) :
    letI := P.category
    Modules P.coefficient ⥤ Modules R :=
  letI := P.category
  { P.modules.functor ⋙ forgetPairs (sigma J s R a) with
    obj M := (P.modules.functor.obj M).obj.a
    map f := (P.modules.functor.map f).hom.f }

/-- Transpose restricted evaluation after the inverse tensor comparison. The map is
constructed without choosing an internal Hom isomorphism.
Source: Stacks, lemma-internal-hom-adjoint-tensor.
(blueprint: lem-sf-twisted-action-restriction-hom-comparison-iso). -/
noncomputable def restrictionHomComparison (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) :
    letI := P.category
    ∀ (M N : Modules P.coefficient),
      (P.modules.functor.obj (SheafOfModules.homObj (R := P.coefficient) M N)).obj.a ⟶
        SheafOfModules.homObj (R := R) (P.modules.functor.obj M).obj.a
          (P.modules.functor.obj N).obj.a :=
  letI := P.category
  fun M N ↦ SheafOfModules.tensorHomEquiv (R := R) _ _ _
    ((T.tensor M (SheafOfModules.homObj (R := P.coefficient) M N)).inv ≫
      (P.modules.functor.map (evaluationMap M N)).hom.f)

private theorem untranspose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N Q : Modules S)
    (f : Q ⟶ SheafOfModules.homObj (R := S) M N) :
    (SheafOfModules.tensorHomEquiv (R := S) M Q N).symm f =
      tensorMap (𝟙 M) f ≫ evaluationMap M N := by
  apply (SheafOfModules.tensorHomEquiv (R := S) M Q N).injective
  simp only [Equiv.apply_symm_apply, tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, evaluationMap, Category.comp_id]

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

private noncomputable def homPair (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N : Pairs (sigma J s R a)) :
    Pairs (sigma J s R a) where
  obj := {
    a := SheafOfModules.homObj (R := R) M.obj.a N.obj.a
    str :=
      (SheafOfModules.tensorHomEquiv (R := R) _ _ _
        ((T.sigmaTensor M.obj.a
          (SheafOfModules.homObj (R := R) M.obj.a N.obj.a)).inv ≫
            (sigma J s R a).map (evaluationMap M.obj.a N.obj.a))) ≫
          SheafOfModules.homObjMap (R := R) (pairIso M).inv (pairIso N).hom }
  property := (homPair_currying J s R a P T M N).1

omit [s.functor.IsContinuous J J] in
private theorem curry_equivariant (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (M N Q : Pairs (sigma J s R a))
    (g : Q.obj.a ⟶ SheafOfModules.homObj (R := R) M.obj.a N.obj.a) :
    (sigma J s R a).map g ≫ (homPair J s R a P T M N).obj.str = Q.obj.str ≫ g ↔
      (sigma J s R a).map (tensorMap (𝟙 M.obj.a) g ≫
          evaluationMap M.obj.a N.obj.a) ≫ N.obj.str =
        (T.sigmaTensor M.obj.a Q.obj.a).hom ≫ tensorMap M.obj.str Q.obj.str ≫
          tensorMap (𝟙 M.obj.a) g ≫ evaluationMap M.obj.a N.obj.a := by
  exact (homPair_currying J s R a P T M N).2 Q g

omit [s.functor.IsContinuous J J] in
private theorem restriction_uncurry (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) :
    letI := P.category
    ∀ (M N Q : Modules P.coefficient)
      (f : Q ⟶ SheafOfModules.homObj (R := P.coefficient) M N),
      (P.modules.functor.map ((SheafOfModules.tensorHomEquiv
        (R := P.coefficient) M Q N).symm f)).hom.f =
      (T.tensor M Q).hom ≫
        tensorMap (𝟙 (P.modules.functor.obj M).obj.a)
          ((P.modules.functor.map f).hom.f ≫ restrictionHomComparison J s R a P T M N) ≫
        evaluationMap (P.modules.functor.obj M).obj.a (P.modules.functor.obj N).obj.a := by
  let := P.category
  intro M N Q f
  let U := underlyingRestriction J s R a P
  apply tensorHomComparison_precomp U T.tensor _ M N Q f
  intro L Q H g
  have h := T.tensor_naturality (𝟙 L) g
  change U.map (tensorMap (𝟙 L) g) ≫ (T.tensor L H).hom =
    (T.tensor L Q).hom ≫ tensorMap (U.map (𝟙 L)) (U.map g) at h
  simpa only [U.map_id] using h

include hs in
/-- The canonical restriction comparison is invertible.
Source: Stacks, sites-modules.tex, section-internal-hom,
lemma-internal-hom-restriction and lemma-internal-hom-adjoint-tensor; restriction
part of steps 11--12 of the twisted action-site construction.
(blueprint: lem-sf-twisted-action-restriction-hom-comparison-iso).

Proof: translation is an equivalence with natural tensor comparisons. The
transpose of translated evaluation is consequently invertible: maps into it are
bijective by full faithfulness, the tensor comparison and the tensor-Hom
adjunction, and essential surjectivity extends this to every test object.
Give Hom(M,N) the composite of this comparison with Hom(theta_M inverse, theta_N).
It is an invertible action. Naturality of the translation tensor comparison and
of the tensor-Hom adjunction shows that a map into this fixed pair is equivariant
if and only if its untranspose is equivariant for the diagonal tensor action.
The tensor-action equation in T therefore makes restrictionHomComparison a
morphism of fixed pairs. Composition with it induces bijections on maps out of
every object in the image of P.modules: the inverse untransposes an equivariant
map, lifts the resulting tensor map by full faithfulness, and transposes it on
the action site. The restriction tensor comparison and its naturality verify
these inverse identities. Essential surjectivity and Yoneda prove that this
fixed-pair morphism is invertible; forgetting its action proves the assertion.
This uses no slice normalization, pure-tensor computation, induction, or choice
of an internal Hom comparison. Zero modules, zero rings and empty sites obey
the same adjunction and equivalence argument. -/
theorem restrictionHomComparison_isIso [HasPullbacks C]
    (P : RestrictionPresentation J s R a) (T : TensorComparisons J s R a P) :
    letI := P.category
    ∀ (M N : Modules P.coefficient), IsIso (restrictionHomComparison J s R a P T M N) := by
  -- Retain the original continuity parameter of the public interface.
  cases hs
  let := P.category
  intro M N
  let F := sigma J s R a
  let E := P.modules.functor
  let U := underlyingRestriction J s R a P
  have hforget : (forgetPairs F).Faithful := by
    change (ObjectProperty.ι _ ⋙ Endofunctor.Algebra.forget F).Faithful
    infer_instance
  have hU : U.Faithful := {
    map_injective := by
      intro X Y f g h
      apply E.map_injective
      apply (forgetPairs F).map_injective
      exact h }
  let H := SheafOfModules.homObj (R := P.coefficient) M N
  let B := homPair J s R a P T (E.obj M) (E.obj N)
  let b := restrictionHomComparison J s R a P T M N
  have he : tensorMap (𝟙 (U.obj M)) b ≫ evaluationMap (U.obj M) (U.obj N) =
      (T.tensor M H).inv ≫ U.map (evaluationMap M N) := by
    rw [← untranspose_evaluation]
    exact (SheafOfModules.tensorHomEquiv (R := R) _ _ _).symm_apply_apply _
  have ht (Q : Modules P.coefficient) :
      F.map (T.tensor M Q).inv ≫ (E.obj (tensorObj M Q)).obj.str =
        (T.sigmaTensor (U.obj M) (U.obj Q)).hom ≫
          tensorMap (E.obj M).obj.str (E.obj Q).obj.str ≫ (T.tensor M Q).inv := by
    apply (cancel_mono (T.tensor M Q).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [T.tensor_action]
    change F.map (T.tensor M Q).inv ≫ F.map (T.tensor M Q).hom ≫ _ = _
    rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  have hb : F.map b ≫ B.obj.str = (E.obj H).obj.str ≫ b := by
    apply (curry_equivariant J s R a P T (E.obj M) (E.obj N) (E.obj H) b).2
    change F.map (tensorMap (𝟙 (U.obj M)) b ≫ evaluationMap (U.obj M) (U.obj N)) ≫
      (E.obj N).obj.str = (T.sigmaTensor (U.obj M) (U.obj H)).hom ≫
        tensorMap (E.obj M).obj.str (E.obj H).obj.str ≫
          tensorMap (𝟙 (U.obj M)) b ≫ evaluationMap (U.obj M) (U.obj N)
    rw [he, F.map_comp, Category.assoc]
    have hn := (E.map (evaluationMap M N)).hom.h
    change F.map (U.map (evaluationMap M N)) ≫ (E.obj N).obj.str =
      (E.obj (tensorObj M H)).obj.str ≫ U.map (evaluationMap M N) at hn
    rw [hn, ← Category.assoc, ht H]
    simp only [Category.assoc]
  let b' : E.obj H ⟶ B := ObjectProperty.homMk { f := b, h := hb }
  have hc (Q : Modules P.coefficient)
      (g : Q ⟶ H) :
      U.map ((SheafOfModules.tensorHomEquiv (R := P.coefficient) M Q N).symm g) =
        (T.tensor M Q).hom ≫ tensorMap (𝟙 (U.obj M)) (U.map g ≫ b) ≫
          evaluationMap (U.obj M) (U.obj N) :=
    restriction_uncurry J s R a P T M N Q g
  have hpost (Q : Modules P.coefficient) :
      Function.Bijective (fun f : E.obj Q ⟶ E.obj H ↦ f ≫ b') := by
    constructor
    · intro f g h
      obtain ⟨f, rfl⟩ := E.map_surjective f
      obtain ⟨g, rfl⟩ := E.map_surjective g
      apply congrArg E.map
      apply (SheafOfModules.tensorHomEquiv (R := P.coefficient) M Q N).symm.injective
      apply U.map_injective
      rw [hc Q f, hc Q g]
      have hh := congrArg ((forgetPairs F).map) h
      change U.map f ≫ b = U.map g ≫ b at hh
      rw [hh]
    · intro f
      let c := tensorMap (𝟙 (U.obj M)) f.hom.f ≫ evaluationMap (U.obj M) (U.obj N)
      have hf : F.map c ≫ (E.obj N).obj.str =
          (T.sigmaTensor (U.obj M) (U.obj Q)).hom ≫
            tensorMap (E.obj M).obj.str (E.obj Q).obj.str ≫ c :=
        (curry_equivariant J s R a P T (E.obj M) (E.obj N) (E.obj Q) f.hom.f).1 f.hom.h
      let e : E.obj (tensorObj M Q) ⟶ E.obj N := ObjectProperty.homMk {
        f := (T.tensor M Q).hom ≫ c
        h := by
          rw [F.map_comp, Category.assoc, hf]
          have ha := T.tensor_action M Q
          change (E.obj (tensorObj M Q)).obj.str ≫ (T.tensor M Q).hom =
            F.map (T.tensor M Q).hom ≫ (T.sigmaTensor (U.obj M) (U.obj Q)).hom ≫
              tensorMap (E.obj M).obj.str (E.obj Q).obj.str at ha
          simpa only [Category.assoc] using congrArg (· ≫ c) ha.symm }
      let k := E.preimage e
      let g := SheafOfModules.tensorHomEquiv (R := P.coefficient) M Q N k
      refine ⟨E.map g, ?_⟩
      apply (forgetPairs F).map_injective
      change U.map g ≫ b = f.hom.f
      apply evaluation_injective (U.obj M) (U.obj N) (U.obj Q)
      apply (cancel_epi (T.tensor M Q).hom).1
      have hk : U.map k = (T.tensor M Q).hom ≫ c :=
        congrArg ((forgetPairs F).map) (E.map_preimage e)
      have hg := hc Q g
      change U.map ((SheafOfModules.tensorHomEquiv (R := P.coefficient) M Q N).symm
        (SheafOfModules.tensorHomEquiv (R := P.coefficient) M Q N k)) = _ at hg
      rw [Equiv.symm_apply_apply] at hg
      exact hg.symm.trans hk
  have hi : IsIso b' := by
    apply isIso_of_yoneda_map_bijective
    intro Q
    let e := E.objObjPreimageIso Q
    constructor
    · intro f g h
      apply (cancel_epi e.hom).1
      apply (hpost (E.objPreimage Q)).1
      simpa only [Category.assoc] using congrArg (e.hom ≫ ·) h
    · intro f
      obtain ⟨g, hg⟩ := (hpost (E.objPreimage Q)).2 (e.hom ≫ f)
      refine ⟨e.inv ≫ g, ?_⟩
      change (e.inv ≫ g) ≫ b' = f
      change g ≫ b' = e.hom ≫ f at hg
      rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact (forgetPairs F).map_isIso b'

end CategoryTheory.TwistedActionRingedSite
