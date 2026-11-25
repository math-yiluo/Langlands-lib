/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceTensorCompatibility
import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceClosedCompatibility

/-! # Restriction compatibility of the normalized adic module comparison -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The complete native/slice comparison, including its normalization under the actual native
pullback and compatibility on every further slice. All fields are conclusions, not hypotheses
on a scheme or on its modules.
Source: Stacks 03EO, 0E8H, 03EL, and native adic pullback and evaluation
(blueprint: lem-sf-adic-module-slice-compatibility). -/
structure AdicModuleSliceCompatibility (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X) where
  /-- Coefficients on the localized site are the restriction of the base coefficients. -/
  coefficientSlice : ∀ (X : Scheme.{u}) (U : X.ProEt),
    (base U.left).ring ≅
      (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring
  /-- The coefficient identification is the identity on each further object's functions. -/
  coefficientSlice_identity : ∀ (X : Scheme.{u}) (U : X.ProEt)
    (V : U.left.ProEtᵒᵖ) (r : (base U.left).ring.obj.obj V),
    HEq (((coefficientSlice X U).hom.hom.app V) r) r
  /-- Native module pullback corresponds naturally to the literal restriction functor. -/
  sliceIso : ∀ (X : Scheme.{u}) (U : X.ProEt),
    adicUpperStar l U.hom ⋙ (base U.left).E.functor ≅
      (base X).E.functor ⋙ adicComparisonRestriction U (base X) (base U.left)
        (coefficientSlice X U)
  /-- Its underlying section map is the canonical inverse-image/localization comparison. -/
  slice_sections : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V),
    ((sliceIso X U).hom.app M).val.app V ((base U.left).sectionsEquiv _ V x) =
      (base X).sectionsEquiv M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x)
  /-- The native balanced tensor comparison along pullback. -/
  nativeTensorSlice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (Mod.tensorLeft ((adicUpperStar l U.hom).obj N)).obj ((adicUpperStar l U.hom).obj M) ≅
      (adicUpperStar l U.hom).obj ((Mod.tensorLeft N).obj M)
  /-- This is the canonical coequalizer comparison, normalized before the quotient. -/
  nativeTensorSlice_quotient : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    Mod.tensorπ ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) ≫
        (nativeTensorSlice X U M N).hom.hom =
      Functor.LaxMonoidal.μ (upperStar (WeilCoefficients.{u} l) U.hom) M.X N.X ≫
        (upperStar (WeilCoefficients.{u} l) U.hom).map (Mod.tensorπ M N)
  /-- The sectionwise balanced tensor comparison along restriction. -/
  tensorSlice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
        ((SheafOfModules.siteSheafTensorRight (A := (base X).R)
          ((base X).E.functor.obj N)).obj ((base X).E.functor.obj M)) ≅
      (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj N))).obj
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj M))
  /-- The restriction comparison preserves the canonical local pure tensors. -/
  tensorSlice_sections : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (x : ((base X).E.functor.obj M).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
    (y : ((base X).E.functor.obj N).val.obj
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (tensorSlice X U M N).hom.val.app V
      (SheafOfModules.siteSheafTensorTmul (A := (base X).R)
        ((base X).E.functor.obj M) ((base X).E.functor.obj N)
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) x y) =
      SheafOfModules.siteSheafTensorTmul (A := (base U.left).R)
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj M))
        ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
          ((base X).E.functor.obj N)) V x y
  /-- The native/sectionwise tensor comparisons commute with restriction. -/
  tensor_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X),
    (base U.left).E.functor.map (nativeTensorSlice X U M N).hom ≫
        (sliceIso X U).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).map
          (((base X).tensorIso N).hom.app M) ≫ (tensorSlice X U M N).hom =
      ((base U.left).tensorIso ((adicUpperStar l U.hom).obj N)).hom.app
          ((adicUpperStar l U.hom).obj M) ≫
        (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
          ((base U.left).E.functor.obj ((adicUpperStar l U.hom).obj N))).map
          ((sliceIso X U).hom.app M) ≫
        SheafOfModules.siteSheafTensorSecondMap (A := (base U.left).R)
          ((adicComparisonRestriction U (base X) (base U.left) (coefficientSlice X U)).obj
            ((base X).E.functor.obj M)) ((sliceIso X U).hom.app N)

  /-- The Hom comparison commutes with restriction, tested on every further slice object.
  The native vertical map is the recorded `adicUpperStarIhomIso`, not an unspecified iso. -/
  hom_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (W : Over V.unop) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj (op W.left)),
    ((sliceIso X U).hom.app N).val.app (op W.left)
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
  /-- Native evaluation commutes with the specified restriction on underlying sections. -/
  evaluation_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ)
    (z : ((adicUpperStar l U.hom).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V),
    adicComparisonPullSection U N V
      (adicComparisonEval ((adicUpperStar l U.hom).obj M) ((adicUpperStar l U.hom).obj N) V
        (((adicUpperStarIhomIso l U.hom M).hom.app N).hom.hom.app V z) x) =
      adicComparisonEval M N
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z)
        (adicComparisonPullSection U M V x)
  /-- Bidual evaluation commutes with restriction through the actual native dual maps. -/
  bidual_slice : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X),
    (adicUpperStar l U.hom).map ((base X).bidual M) ≫
        adicComparisonDualSlice U ((AdicSheaf.ihom M).obj (AdicSheaf.unit l X)) =
      (base U.left).bidual ((adicUpperStar l U.hom).obj M) ≫
        (Mod.ihomMap (adicComparisonDualSlice U M)).app (AdicSheaf.unit l U.left)
private theorem tensorSlice_square (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (r : AdicSliceRestrictionData l base c)
    (X : Scheme.{u}) (U : X.ProEt) (M N : AdicSheaf l X) :
    (base U.left).E.functor.map (adicSliceNativeTensorIso U M N).hom ≫
        (r.sliceIso X U).hom.app ((Mod.tensorLeft N).obj M) ≫
        (adicComparisonRestriction U (base X) (base U.left) (c X U)).map
          (((base X).tensorIso N).hom.app M) ≫ (adicSliceTensorIso l base c r X U M N).hom =
      ((base U.left).tensorIso ((adicUpperStar l U.hom).obj N)).hom.app
          ((adicUpperStar l U.hom).obj M) ≫
        (SheafOfModules.siteSheafTensorRight (A := (base U.left).R)
          ((base U.left).E.functor.obj ((adicUpperStar l U.hom).obj N))).map
          ((r.sliceIso X U).hom.app M) ≫
        SheafOfModules.siteSheafTensorSecondMap (A := (base U.left).R)
          ((adicComparisonRestriction U (base X) (base U.left) (c X U)).obj
            ((base X).E.functor.obj M)) ((r.sliceIso X U).hom.app N) := by
  let a := ((base U.left).E.functor.mapIso (adicSliceNativeTensorIso U M N)) ≪≫
    (r.sliceIso X U).app ((Mod.tensorLeft N).obj M) ≪≫
    (adicComparisonRestriction U (base X) (base U.left) (c X U)).mapIso
      (((base X).tensorIso N).app M)
  calc
    _ = a.hom ≫ (adicSliceTensorIso l base c r X U M N).hom := by
      simp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    _ = _ := by
      change a.hom ≫ (a.inv ≫ _) = _
      rw [Iso.hom_inv_id_assoc]
      rfl

/-- A normalized comparison commutes with the actual site-object inverse image.
Source: Stacks Project, Tags 03CE, 03EL and 0E8H
(blueprint: lem-sf-adic-module-slice-compatibility).

Proof: identify the pro-etale site of a site object with the slice site. On each
further object the coefficient functions and their restriction maps coincide.
The initial indexing object for inverse image makes the actual coefficient map
identity on these functions. The monoidal inverse-image comparison preserves pure
tensors, so it carries the action to the restricted action. Extension of scalars
along this coefficient isomorphism has inverse m ↦ 1 ⊗ m; the balanced relation
r ⊗ m = 1 ⊗ rm proves the two inverse identities. This gives the normalized natural
module restriction comparison. The universal property of the balanced tensor gives
its native pullback comparison; the localized sheaf tensor comparison preserves
pure tensors. Testing on pure tensors proves their commutative square. On a further
slice, both internal-Hom comparisons identify the very same module morphisms on
that slice. Currying restricted evaluation therefore gives exactly the recorded
native Hom pullback map; uniqueness of transposes proves the Hom equation on every
further object. At the identity slice this Hom equation, combined with the base
evaluation formulas and injectivity of the additive section identification, proves
the evaluation restriction formula. Applying the same uniqueness to braided evaluation proves the
bidual restriction equation. The normalization of a supplied base comparison pins
all its maps by their sections, pure tensors and counits, so this argument applies
to every such base family. -/
theorem adicModuleSliceCompatibility (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X) :
    Nonempty (AdicModuleSliceCompatibility l base) := by
  obtain ⟨c, hc⟩ := adicSliceCoefficientComparison l base
  obtain ⟨r⟩ := adicSliceRestrictionComparison l base c hc
  have h := adicSliceClosedCompatibility l base c r
  refine ⟨{
    coefficientSlice := c
    coefficientSlice_identity := hc
    sliceIso := r.sliceIso
    slice_sections := r.slice_sections
    nativeTensorSlice := fun _ U M N ↦ adicSliceNativeTensorIso U M N
    nativeTensorSlice_quotient := fun _ U M N ↦ adicSliceNativeTensorIso_quotient U M N
    tensorSlice := adicSliceTensorIso l base c r
    tensorSlice_sections := adicSliceTensorIso_sections l base c r
    tensor_slice := tensorSlice_square l base c r
    hom_slice := h.hom_slice
    evaluation_slice := ?_
    bidual_slice := h.bidual_slice }⟩
  intro X U M N V z x
  apply ((base X).sectionsEquiv N
    (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))).injective
  rw [← r.slice_sections X U N V, (base U.left).evaluation]
  have hh := h.hom_slice X U M N V z (Over.mk (𝟙 V.unop)) x
  have he := (base X).evaluation M N
    (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
    (adicComparisonPullSection U ((AdicSheaf.ihom M).obj N) V z)
    (adicComparisonPullSection U M V x)
  simpa only [Functor.map_id, Over.mk_left, op_unop] using hh.trans he.symm

end AlgebraicGeometry.ProEtale
