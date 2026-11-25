/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison

/-! # Coefficient identification on a pro-etale site object -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale

/-- Normalized coefficient sheaves restrict by the identity on function sections.
Source: Stacks 03CV, and the coefficient normalization of the base comparison
(blueprint: lem-sf-adic-slice-coefficients).

Proof: on each object compose the coefficient identification at its source with
 the inverse coefficient identification after composition to the base. Both are
 the same locally finite functions on the same underlying scheme. Naturality is
 precomposition of functions on either side. The supplied identity conditions
 show that the resulting map leaves every function unchanged. -/
theorem adicSliceCoefficientComparison (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X) :
    ∃ c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring,
      ∀ (X : Scheme.{u}) (U : X.ProEt) (V : U.left.ProEtᵒᵖ)
        (r : (base U.left).ring.obj.obj V), HEq (((c X U).hom.hom.app V) r) r := by
  let e (X : Scheme.{u}) (U : X.ProEt) (V : U.left.ProEtᵒᵖ) :=
    (base U.left).coefficient V |>.trans
      ((base X).coefficient
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))).symm
  have hn (X : Scheme.{u}) (U : X.ProEt) {V W : U.left.ProEtᵒᵖ} (f : V ⟶ W)
      (r : (base U.left).ring.obj.obj V) :
      e X U W ((base U.left).ring.obj.map f r) =
        (((localizationRestriction RingCat.{u + 1} U.hom U.prop).obj
          (base X).ring).obj.map f) (e X U V r) := by
    apply ((base X).coefficient
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.unop))).injective
    calc
      _ = (base U.left).coefficient W ((base U.left).R.obj.map f r) :=
        RingEquiv.apply_symm_apply _ _
      _ = WeilCoefficients.uliftAlgHom
          (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l f.unop.left.base.hom)
          ((base U.left).coefficient V r) :=
        (base U.left).coefficient_naturality f r
      _ = _ := by
        have h := (base X).coefficient_naturality
          ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).op.map f) (e X U V r)
        have he : (base X).coefficient
            (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
            (e X U V r) = (base U.left).coefficient V r :=
          RingEquiv.apply_symm_apply _ _
        exact (h.trans (congrArg (WeilCoefficients.uliftAlgHom
          (PadicAlgCl.locallyFiniteFunctionsCompAlgHom l f.unop.left.base.hom)) he)).symm
  let c (X : Scheme.{u}) (U : X.ProEt) :
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun V ↦ (e X U V).toRingCatIso) (by
        intro V W f
        ext r
        exact hn X U f r))
  refine ⟨c, ?_⟩
  intro X U V r
  change HEq (e X U V r) r
  have h := (base X).coefficient_identity
    (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) (e X U V r)
  have he : (base X).coefficient
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) (e X U V r) =
      (base U.left).coefficient V r := by
    exact RingEquiv.apply_symm_apply _ _
  exact h.symm.trans ((heq_of_eq he).trans ((base U.left).coefficient_identity V r))

end AlgebraicGeometry.ProEtale
