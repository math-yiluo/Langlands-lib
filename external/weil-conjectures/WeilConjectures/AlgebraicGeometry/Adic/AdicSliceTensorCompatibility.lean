/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceRestrictionComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceNativeTensorComparison

/-! # Balanced tensors and normalized module restriction -/

@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The sectionwise tensor comparison obtained from the two normalized base comparisons
and native tensor pullback. Its defining composite makes the tensor square commute.
Source: Stacks 03EL and the native balanced tensor comparison
(blueprint: lem-sf-adic-slice-tensor). -/
noncomputable def adicSliceTensorIso (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c)
    (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X) :
    (adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
        ((SheafOfModules.siteSheafTensorRight (A := (base X).R)
          ((base X).E.functor.obj N)).obj ((base X).E.functor.obj M)) ≅
      (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
          ((base X).E.functor.obj N))).obj
        ((adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
          ((base X).E.functor.obj M)) := by
  let P := base X
  let Q := base U.left
  let F := adicComparisonRestriction U P Q (c X U)
  let S := F.obj (P.E.functor.obj M)
  let sn := (r.sliceIso X U).app N
  let ep : SheafOfModules.siteTensorPresheaf (R := Q.R.obj) S.val
      (Q.E.functor.obj ((adicUpperStar l U.hom).obj N)).val ≅
      SheafOfModules.siteTensorPresheaf (R := Q.R.obj) S.val
        (F.obj (P.E.functor.obj N)).val :=
    { hom := SheafOfModules.siteTensorSecondMap S.val sn.hom.val
      inv := SheafOfModules.siteTensorSecondMap S.val sn.inv.val
      hom_inv_id := by
        ext V : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change x ⊗ₜ[Q.R.obj.obj V] (sn.inv.val.app V (sn.hom.val.app V y)) = x ⊗ₜ y
        exact congrArg (fun z ↦ x ⊗ₜ[Q.R.obj.obj V] z)
          (ConcreteCategory.congr_hom
            (congrArg (fun k ↦ k.val.app V) sn.hom_inv_id) y)
      inv_hom_id := by
        ext V : 1
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change x ⊗ₜ[Q.R.obj.obj V] (sn.hom.val.app V (sn.inv.val.app V y)) = x ⊗ₜ y
        exact congrArg (fun z ↦ x ⊗ₜ[Q.R.obj.obj V] z)
          (ConcreteCategory.congr_hom
            (congrArg (fun k ↦ k.val.app V) sn.inv_hom_id) y) }
  exact ((Q.E.functor.mapIso (adicSliceNativeTensorIso U M N)) ≪≫
      (r.sliceIso X U).app ((Mod.tensorLeft N).obj M) ≪≫
        F.mapIso ((P.tensorIso N).app M)).symm ≪≫
    ((Q.tensorIso ((adicUpperStar l U.hom).obj N)).app ((adicUpperStar l U.hom).obj M)) ≪≫
    (SheafOfModules.siteSheafTensorRight (A := Q.R)
      (Q.E.functor.obj ((adicUpperStar l U.hom).obj N))).mapIso ((r.sliceIso X U).app M) ≪≫
    (PresheafOfModules.sheafification (R := Q.ring) (𝟙 _)).mapIso ep

private lemma nativeTensor_pullSection {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (M N : AdicSheaf l X) (V : U.left.ProEtᵒᵖ)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V)
    (y : ((adicUpperStar l U.hom).obj N).X.obj.obj V) :
    adicComparisonPullSection U ((Mod.tensorLeft N).obj M) V
      ((adicSliceNativeTensorIso U M N).hom.hom.hom.app V
        (adicComparisonTmul ((adicUpperStar l U.hom).obj M)
          ((adicUpperStar l U.hom).obj N) V x y)) =
      adicComparisonTmul M N
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x) (adicComparisonPullSection U N V y) := by
  let : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  let A := WeilCoefficients.{u} l
  let e := upperStarIsoSheafPushforward A U.hom U.prop
  let F := (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).sheafPushforwardContinuous
    A (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X)
  have hq : Mod.tensorπ ((adicUpperStar l U.hom).obj M)
        ((adicUpperStar l U.hom).obj N) ≫
      (adicSliceNativeTensorIso U M N).hom.hom ≫ e.hom.app ((Mod.tensorLeft N).obj M).X =
      (e.hom.app M.X ⊗ₘ e.hom.app N.X) ≫
        Functor.LaxMonoidal.μ F M.X N.X ≫ F.map (Mod.tensorπ M N) := by
    rw [← Category.assoc, adicSliceNativeTensorIso_quotient, Category.assoc,
      e.hom.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor, Category.assoc]
    rfl
  have hn := Sheaf.tensorObjComparison_naturality (J := Scheme.ProEt.topology U.left)
    (e.hom.app M.X) (e.hom.app N.X)
  have hr := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop) A
    (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) M.X N.X V
  have hq' := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app V) hq)
    ((Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
      ((adicUpperStar l U.hom).obj M).X ((adicUpperStar l U.hom).obj N).X).app V
        (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))
  have hn' := congrArg (fun f ↦ ModuleCat.Hom.hom (f.app V)
    (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y)) hn
  change (e.hom.app M.X ⊗ₘ e.hom.app N.X).hom.app V
      ((Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left)
        ((adicUpperStar l U.hom).obj M).X ((adicUpperStar l U.hom).obj N).X).app V
          (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y)) =
    (Sheaf.tensorObjComparison (Scheme.ProEt.topology U.left) (F.obj M.X) (F.obj N.X)).app V
      ((e.hom.app M.X).hom.app V x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)]
        (e.hom.app N.X).hom.app V y) at hn'
  have hr' := ConcreteCategory.congr_hom hr
    ((e.hom.app M.X).hom.app V x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)]
      (e.hom.app N.X).hom.app V y)
  exact hq'.trans ((congrArg (fun z ↦ (F.map (Mod.tensorπ M N)).hom.app V
    ((Functor.LaxMonoidal.μ F M.X N.X).hom.app V z)) hn').trans
      (congrArg (fun z ↦ (F.map (Mod.tensorπ M N)).hom.app V z) hr'))

private lemma tensor_map_first {X : Scheme.{u}}
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    {M M' N : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)} (f : M ⟶ M')
    (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((SheafOfModules.siteSheafTensorRight (A := A) N).map f).val.app V
      (SheafOfModules.siteSheafTensorTmul (A := A) M N V x y) =
      SheafOfModules.siteSheafTensorTmul (A := A) M' N V (f.val.app V x) y := by
  exact (congrArg (fun q ↦ q.app V (x ⊗ₜ[A.obj.obj V] y))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) (𝟙 _)).unit.naturality
        (SheafOfModules.siteTensorHom f.val N.val))).symm

private lemma tensor_map_second {X : Scheme.{u}}
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    {M N N' : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)} (g : N ⟶ N')
    (V : X.ProEtᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (SheafOfModules.siteSheafTensorSecondMap (A := A) M g).val.app V
      (SheafOfModules.siteSheafTensorTmul (A := A) M N V x y) =
      SheafOfModules.siteSheafTensorTmul (A := A) M N' V x (g.val.app V y) := by
  exact (congrArg (fun q ↦ q.app V (x ⊗ₜ[A.obj.obj V] y))
    ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) (𝟙 _)).unit.naturality
        (SheafOfModules.siteTensorSecondMap M.val g.val))).symm

private lemma adicSliceTensorIso_hom (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c)
    (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X) :
    (adicSliceTensorIso l base c r X U M N).hom =
      let P := base X
      let Q := base U.left
      let F := adicComparisonRestriction U P Q (c X U)
      let m := (adicUpperStar l U.hom).obj M
      let n := (adicUpperStar l U.hom).obj N
      ((Q.E.functor.mapIso (adicSliceNativeTensorIso U M N)) ≪≫
        (r.sliceIso X U).app ((Mod.tensorLeft N).obj M) ≪≫
          F.mapIso ((P.tensorIso N).app M)).inv ≫
      ((Q.tensorIso n).app m).hom ≫
      (SheafOfModules.siteSheafTensorRight (A := Q.R) (Q.E.functor.obj n)).map
        ((r.sliceIso X U).app M).hom ≫
      SheafOfModules.siteSheafTensorSecondMap (A := Q.R) (F.obj (P.E.functor.obj M))
        ((r.sliceIso X U).app N).hom := by
  rfl

/-- The explicitly constructed tensor restriction iso preserves local pure tensors.
Source: Stacks 03EL and 0E8H; the pure-tensor test in step 2 of the parent comparison.
(blueprint: lem-sf-adic-slice-tensor).

Proof: native tensor pullback is normalized by its equation before the balanced
quotient. The native inverse-image/localization comparison is monoidal, so on
local pure tensors it gives the same underlying restricted sections in each
factor. Insert the base tensor_sections formulas and the restriction
slice_sections formulas into the defining composite of adicSliceTensorIso.
The second-factor tensor map sends x ⊗ y to x ⊗ sn(y), and the first-factor
map has the analogous formula. The quotient equation and the two base
normalizations therefore cancel the inverse part of that composite on a pure
tensor. What remains is exactly the local pure tensor on the restricted site.
Equivalently use exists_localizedSiteTensorRestriction on the actual slice
site: its iso preserves pure tensors, and its composite with the native and
base comparisons is the same by the coequalizer universal property, so equals
the explicitly constructed iso. This proof applies to arbitrary modules and
includes their zero sections. -/
theorem adicSliceTensorIso_sections (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c)
    (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (x : ((base X).E.functor.obj M).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
    (y : ((base X).E.functor.obj N).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))) :
    (adicSliceTensorIso l base c r X U M N).hom.val.app V
      (SheafOfModules.siteSheafTensorTmul (A := (base X).R)
        ((base X).E.functor.obj M) ((base X).E.functor.obj N)
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) x y) =
      SheafOfModules.siteSheafTensorTmul (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
          ((base X).E.functor.obj M))
        ((adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
          ((base X).E.functor.obj N)) V x y := by
  rw [adicSliceTensorIso_hom]
  let P := base X
  let Q := base U.left
  let F := adicComparisonRestriction U P Q (c X U)
  let m := (adicUpperStar l U.hom).obj M
  let n := (adicUpperStar l U.hom).obj N
  let W := op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)
  let sm := (r.sliceIso X U).app M
  let sn := (r.sliceIso X U).app N
  obtain ⟨a, ha⟩ := (Q.sectionsEquiv m V).surjective (sm.inv.val.app V x)
  obtain ⟨b, hb⟩ := (Q.sectionsEquiv n V).surjective (sn.inv.val.app V y)
  have hx : sm.hom.val.app V (Q.sectionsEquiv m V a) = x := by
    exact (congrArg (fun t ↦ sm.hom.val.app V t) ha).trans
      (congrArg (fun f ↦ f.val.app V x) sm.inv_hom_id)
  have hy : sn.hom.val.app V (Q.sectionsEquiv n V b) = y := by
    exact (congrArg (fun t ↦ sn.hom.val.app V t) hb).trans
      (congrArg (fun f ↦ f.val.app V y) sn.inv_hom_id)
  let d := (Q.E.functor.mapIso (adicSliceNativeTensorIso U M N)) ≪≫
    (r.sliceIso X U).app ((Mod.tensorLeft N).obj M) ≪≫
      F.mapIso ((P.tensorIso N).app M)
  let z := Q.sectionsEquiv _ V (adicComparisonTmul m n V a b)
  have hd : d.hom.val.app V z =
      SheafOfModules.siteSheafTensorTmul (A := P.R)
        (P.E.functor.obj M) (P.E.functor.obj N) W x y := by
    as_aux_lemma =>
      change ((P.tensorIso N).hom.app M).val.app W
        (((r.sliceIso X U).hom.app ((Mod.tensorLeft N).obj M)).val.app V
          ((Q.E.functor.map (adicSliceNativeTensorIso U M N).hom).val.app V z)) = _
      have hmap := Q.section_map (adicSliceNativeTensorIso U M N).hom V
        (adicComparisonTmul m n V a b)
      have hs := r.slice_sections X U ((Mod.tensorLeft N).obj M) V
        ((adicSliceNativeTensorIso U M N).hom.hom.hom.app V
          (adicComparisonTmul m n V a b))
      have ht := nativeTensor_pullSection U M N V a b
      have hp := (congrArg
        (fun t ↦ ((r.sliceIso X U).hom.app ((Mod.tensorLeft N).obj M)).val.app V t)
        hmap.symm).trans (hs.trans (congrArg (P.sectionsEquiv _ W) ht))
      exact (congrArg (fun t ↦ ((P.tensorIso N).hom.app M).val.app W t) hp).trans
        ((P.tensor_sections M N W (adicComparisonPullSection U M V a)
          (adicComparisonPullSection U N V b)).trans
          (congrArg₂ (SheafOfModules.siteSheafTensorTmul (A := P.R)
            (P.E.functor.obj M) (P.E.functor.obj N) W)
            ((r.slice_sections X U M V a).symm.trans hx)
            ((r.slice_sections X U N V b).symm.trans hy)))
  let k := ((Q.tensorIso n).app m).hom ≫
    (SheafOfModules.siteSheafTensorRight (A := Q.R) (Q.E.functor.obj n)).map sm.hom ≫
      SheafOfModules.siteSheafTensorSecondMap (A := Q.R) (F.obj (P.E.functor.obj M)) sn.hom
  have hdid : d.inv.val.app V (d.hom.val.app V z) = z :=
    congrArg (fun f ↦ f.val.app V z) d.hom_inv_id
  refine (congrArg (fun t ↦ k.val.app V (d.inv.val.app V t)) hd.symm).trans ?_
  refine (congrArg (fun t ↦ k.val.app V t) hdid).trans ?_
  have hfirst := tensor_map_first (X := U.left) Q.R
    (M := Q.E.functor.obj m) (M' := F.obj (P.E.functor.obj M))
    (N := Q.E.functor.obj n) sm.hom V (Q.sectionsEquiv m V a) (Q.sectionsEquiv n V b)
  have hsecond := tensor_map_second (X := U.left) Q.R
    (M := F.obj (P.E.functor.obj M)) (N := Q.E.functor.obj n)
    (N' := F.obj (P.E.functor.obj N)) sn.hom V
    (sm.hom.val.app V (Q.sectionsEquiv m V a)) (Q.sectionsEquiv n V b)
  exact (congrArg (fun t ↦ (SheafOfModules.siteSheafTensorSecondMap (A := Q.R)
    (F.obj (P.E.functor.obj M)) sn.hom).val.app V
      (((SheafOfModules.siteSheafTensorRight (A := Q.R) (Q.E.functor.obj n)).map
        sm.hom).val.app V t)) (Q.tensor_sections m n V a b)).trans
    ((congrArg (fun t ↦ (SheafOfModules.siteSheafTensorSecondMap (A := Q.R)
      (F.obj (P.E.functor.obj M)) sn.hom).val.app V t) hfirst).trans
        (hsecond.trans (congrArg₂ (SheafOfModules.siteSheafTensorTmul (A := Q.R)
          (F.obj (P.E.functor.obj M)) (F.obj (P.E.functor.obj N)) V) hx hy)))

end AlgebraicGeometry.ProEtale
