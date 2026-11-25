/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceRestrictionComparison
import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry

/-! # Closed comparisons on further pro-etale slices -/

@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The two closed compatibility equations, without a bidual invertibility assertion.
Source: Stacks 03CE, 03EL, 03EO and 0E8H (blueprint: lem-sf-adic-slice-closed). -/
structure AdicSliceClosedData (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c) : Prop where
  /-- The Hom comparison commutes with restriction, tested on every further slice object.
  The native vertical map is the recorded `adicUpperStarIhomIso`, not an unspecified iso. -/
  hom_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (W : Over V.unop) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj (op W.left)),
    ((r.sliceIso X U).hom.app N).val.app (op W.left)
      (((((base U.left).homIso ((adicUpperStar l U.hom).obj M)).hom.app
          ((adicUpperStar l U.hom).obj N)).val.app V
        ((base U.left).sectionsEquiv _ V
          (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.app V z))).app (op W)
            ((base U.left).sectionsEquiv _ (op W.left) x)) =
      ((((base X).homIso M).hom.app N).val.app
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        ((base X).sectionsEquiv _
          (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
          (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z))).app
            (op (Over.mk ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).map W.hom)))
              ((base X).sectionsEquiv M
                (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.left))
                (adicComparisonPullSection U M (op W.left) x))
  /-- Bidual evaluation commutes with restriction through the actual native dual maps. -/
  bidual_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X),
    (adicUpperStar l U.hom).map ((base X).bidual M) ≫
        adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) =
      (base U.left).bidual ((adicUpperStar l U.hom).obj M) ≫
        (Mod.ihomMap (adicComparisonDualSlice U M)).app (AdicSheaf.unit l U.left)

attribute [local irreducible] Sheaf.tensorObjComparison adicUpperStarIhomIso

section
variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

private lemma hom_sections (P : AdicModuleSectionComparison l X)
    (M N : AdicSheaf l X) (V : X.ProEtᵒᵖ)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (W : Over V.unop) (x : M.X.obj.obj (op W.left)) :
    (((P.homIso M).hom.app N).val.app V (P.sectionsEquiv _ V z)).app (op W)
        (P.sectionsEquiv M (op W.left) x) =
      P.sectionsEquiv N (op W.left)
        (adicComparisonEval M N (op W.left)
          (((AdicSheaf.ihom M).obj N).X.obj.map W.hom.op z) x) := by
  have h := PresheafOfModules.naturality_apply ((P.homIso M).hom.app N).val
    W.hom.op (P.sectionsEquiv _ V z)
  change (((P.homIso M).hom.app N).val.app (op W.left))
      ((P.E.functor.obj ((AdicSheaf.ihom M).obj N)).val.map W.hom.op
        (P.sectionsEquiv _ V z)) = _ at h
  rw [← P.section_restriction] at h
  have hh := congrArg (fun t ↦ t.app (op (Over.mk (𝟙 W.left)))
    (P.sectionsEquiv M (op W.left) x)) h
  exact (PresheafOfModules.restrictOver_hom_app_congr
    (((P.homIso M).hom.app N).val.app V (P.sectionsEquiv _ V z))
    (Category.id_comp W.hom) _).symm.trans
      (hh.symm.trans (P.evaluation M N (op W.left) _ x).symm)

private lemma restriction_tensor (U : X.ProEt)
    (P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (V : U.left.ProEtᵒᵖ) :
    (Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
      ((upperStar (WeilCoefficients.{u} l) U.hom).obj P)
      ((upperStar (WeilCoefficients.{u} l) U.hom).obj Q)).app V ≫
        (Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom) P Q).hom.app V ≫
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
          U.hom U.prop).hom.app (P ⊗ Q)).hom.app V =
      (((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
          U.hom U.prop).hom.app P).hom.app V ⊗ₘ
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
          U.hom U.prop).hom.app Q).hom.app V) ≫
      (Sheaf.tensorObjComparison (Scheme.ProEt.topology X) P Q).app
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) := by
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (V := U.left) (U := X) U.prop
  have h := NatTrans.IsMonoidal.tensor
    (τ := (upperStarIsoSheafPushforward (WeilCoefficients.{u} l) U.hom U.prop).hom) P Q
  have hh := congrArg (fun f ↦ f.hom.app V) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hh
  simp only [upperStarIsoSheafPushforward] at hh
  rw [hh, ← Category.assoc]
  have hn := congr_app (Sheaf.tensorObjComparison_naturality
    ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
      U.hom U.prop).hom.app P)
    ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
      U.hom U.prop).hom.app Q)) V
  simp only [NatTrans.comp_app, Monoidal.tensorHom_app] at hn
  erw [hn, Category.assoc]
  congr 1
  unfold Sheaf.tensorObjComparison
  exact Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop) (WeilCoefficients.{u} l)
    (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) P Q V

private lemma evaluation_restriction (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V) :
    adicComparisonPullSection U N V
      (adicComparisonEval ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) V
        (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.app V z) x) =
      adicComparisonEval M N
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z)
        (adicComparisonPullSection U M V x) := by
  have he := congrArg (fun f ↦ f.hom.app V) (adicUpperStarIhomIso_evaluation U.hom M N)
  have hn := congrArg (fun f ↦ f.hom.app V)
    ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
      U.hom U.prop).hom.naturality (Mod.evaluation M N))
  have ht := restriction_tensor U ((AdicSheaf.ihom M).obj N).X M.X V
  have hmap := congr_app (Sheaf.tensorObjComparison_naturality
    ((adicUpperStarIhomIso l U.hom M).hom.app N).hom
    (𝟙 ((adicUpperStar l U.hom).obj M).X)) V
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Monoidal.tensorHom_app] at he hn hmap
  have h := congrArg (fun f ↦ f ≫
    (Mod.evaluation ((adicUpperStar l U.hom).obj M)
      ((adicUpperStar l U.hom).obj N)).hom.app V ≫
    ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
      U.hom U.prop).hom.app N.X).hom.app V) hmap
  simp only [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, tensorHom_id] at h
  change ((Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
    ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X
    ((adicUpperStar l U.hom).obj M).X).app V ≫
      (((adicUpperStarIhomIso l U.hom M).hom.app N).hom ▷
        ((adicUpperStar l U.hom).obj M).X).hom.app V) ≫ _ = _ at h
  simp only [Category.assoc] at h
  erw [reassoc_of% he, hn, reassoc_of% ht] at h
  have hv := congrArg (fun f ↦ ModuleCat.Hom.hom f
    (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)) h
  exact hv.symm

private lemma dual_evaluation (U : X.ProEt) (M : AdicSheaf l X) :
    (adicComparisonDualSlice U M).hom ▷ ((adicUpperStar l U.hom).obj M).X ≫
        Mod.evaluation ((adicUpperStar l U.hom).obj M) (AdicSheaf.unit l U.left) =
      Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom)
          ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)).X M.X ≫
        (upperStar (WeilCoefficients.{u} l) U.hom).map
          (Mod.evaluation M (AdicSheaf.unit l X)) ≫ (adicUpperStarUnitIso l U.hom).hom.hom := by
  simp only [adicComparisonDualSlice, Mod.comp_hom', comp_whiskerRight, Category.assoc]
  erw [Mod.evaluation_naturality ((adicUpperStar l U.hom).obj M)
    (adicUpperStarUnitIso l U.hom).hom]
  erw [← Category.assoc, adicUpperStarIhomIso_evaluation U.hom M
    (AdicSheaf.unit l X), Category.assoc]

attribute [local irreducible] adicComparisonDualSlice Mod.ihomMap Mod.evaluation

private lemma bidual_restriction (U : X.ProEt)
    (P : AdicModuleSectionComparison l X) (Q : AdicModuleSectionComparison l U.left)
    (M : AdicSheaf l X) :
    (adicUpperStar l U.hom).map (P.bidual M) ≫
        adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) =
      Q.bidual ((adicUpperStar l U.hom).obj M) ≫
        (Mod.ihomMap (adicComparisonDualSlice U M)).app (AdicSheaf.unit l U.left) := by
  apply Mod.Hom.ext
  apply Mod.hom_ext_of_evaluation
  simp only [Mod.comp_hom', comp_whiskerRight, Category.assoc]
  rw [dual_evaluation]
  rw [adicUpperStar_map_hom]
  erw [Functor.LaxMonoidal.μ_natural_left_assoc]
  erw [← Functor.map_comp_assoc, P.bidual_transpose, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.LaxBraided.braided_assoc]
  rw [← dual_evaluation]
  rw [Mod.evaluation_ihomMap (adicComparisonDualSlice U M) (AdicSheaf.unit l U.left)]
  rw [← whisker_exchange_assoc, Q.bidual_transpose]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rfl

end

/-- Internal Hom on further slices and bidual evaluation respect native pullback.
Source: Stacks 03EO and 0E8H; step 2 of the parent comparison.
(blueprint: lem-sf-adic-slice-closed).

Proof: after identifying the object site with the localized site, a section
of internal Hom is exactly a linear morphism on the further slice. Use the
normalized restriction comparison to identify these morphisms on both sides.
The transpose of restricted evaluation defines the comparison. The native
adicUpperStarIhomIso preserves evaluation, so the uniqueness of a transpose
identifies this comparison with that specified native map. Evaluate the
resulting equality of further-slice morphisms on a section to obtain hom_slice.
For biduality apply the same argument to evaluation with the two factors
exchanged. Both displayed composites are transposes of that same braided
evaluation: the base bidual_transpose formulas give the base transposes, the
native Hom comparison preserves evaluation, and the unit pullback identifies
the regular modules. Uniqueness under the tensor/Hom adjunction proves the
bidual equation. No invertibility or finite-rank assertion for biduality is
used. -/
theorem adicSliceClosedCompatibility (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c) :
    AdicSliceClosedData l base c r := by
  refine ⟨?_, fun X U M ↦ bidual_restriction U (base X) (base U.left) M⟩
  intro X U M N V z W x
  rw [hom_sections, r.slice_sections]
  erw [hom_sections]
  have hn := ConcreteCategory.congr_hom
    (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.naturality W.hom.op) z
  have hp := ConcreteCategory.congr_hom
    (((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l)
      U.hom U.prop).hom.app ((AdicSheaf.ihom M).obj N).X).hom.naturality W.hom.op) z
  simp only [ConcreteCategory.comp_apply, op_unop] at hn hp
  apply congrArg ((base X).sectionsEquiv N
    (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.left)))
  erw [← hn]
  exact (evaluation_restriction U M N (op W.left) _ x).trans
    (congrArg (fun t ↦ adicComparisonEval M N
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.left)) t
      (adicComparisonPullSection U M (op W.left) x)) hp)

end AlgebraicGeometry.ProEtale
