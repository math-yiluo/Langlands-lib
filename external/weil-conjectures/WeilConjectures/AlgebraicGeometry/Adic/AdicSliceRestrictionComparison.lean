/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleSectionComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicSliceRestrictionSections

/-! # Normalized module restriction on a site object -/

@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The conclusions of the restriction step for AdicSliceRestrictionData.
Source: Stacks 03CE, 03EL, 03EO and 0E8H (blueprint: lem-sf-adic-slice-restriction). -/
structure AdicSliceRestrictionData (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring) where
  /-- Native module pullback corresponds naturally to the literal restriction functor. -/
  sliceIso : ∀ (X : Scheme.{u}) (U : X.ProEt),
    adicUpperStar l U.hom ⋙ (base U.left).E.functor ≅
      (base X).E.functor ⋙ adicComparisonRestriction U (base X) (base U.left)
        (c X U)
  /-- Its underlying section map is the canonical inverse-image/localization comparison. -/
  slice_sections : ∀ (X : Scheme.{u}) (U : X.ProEt) (M : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V),
    ((sliceIso X U).hom.app M).val.app V ((base U.left).sectionsEquiv _ V x) =
      (base X).sectionsEquiv M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x)

section
variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (U : X.ProEt) (P : AdicModuleSectionComparison l X)
    (Q : AdicModuleSectionComparison l U.left)
    (c : Q.ring ≅ (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj P.ring)
    (hc : ∀ (V : U.left.ProEtᵒᵖ) (a : Q.ring.obj.obj V), HEq ((c.hom.hom.app V) a) a)

include hc in
private noncomputable def restrictionLinearEquiv (M : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ) :
    (Q.E.functor.obj ((adicUpperStar l U.hom).obj M)).val.obj V ≃ₗ[
      Q.ring.obj.obj V]
      ((adicComparisonRestriction U P Q c).obj
        (P.E.functor.obj M)).val.obj V :=
  { adicSliceSectionEquiv U P Q c M V with
    map_smul' := adicSliceSectionEquiv_smul U P Q c hc M V }

include hc in
private lemma restrictionLinearEquiv_apply (M : AdicSheaf l X)
    (V : U.left.ProEtᵒᵖ) (x : ((adicUpperStar l U.hom).obj M).X.obj.obj V) :
    restrictionLinearEquiv U P Q c hc M V (Q.sectionsEquiv _ V x) =
      P.sectionsEquiv M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x) := by
  exact congrArg (fun y ↦ P.sectionsEquiv M
    (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
    (adicComparisonPullSection U M V y))
    ((Q.sectionsEquiv _ V).symm_apply_apply x)

include hc in
private lemma restrictionLinearEquiv_naturality (M : AdicSheaf l X)
    {V W : U.left.ProEtᵒᵖ} (f : V ⟶ W)
    (y : (Q.E.functor.obj ((adicUpperStar l U.hom).obj M)).val.obj V) :
    restrictionLinearEquiv U P Q c hc M W
        ((Q.E.functor.obj ((adicUpperStar l U.hom).obj M)).val.map f y) =
      ((adicComparisonRestriction U P Q c).obj
        (P.E.functor.obj M)).val.map f (restrictionLinearEquiv U P Q c hc M V y) := by
  obtain ⟨x, rfl⟩ := (Q.sectionsEquiv _ V).surjective y
  have hh := ConcreteCategory.congr_hom
    (((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop).hom.app
      M.X).hom.naturality f) x
  calc
    _ = restrictionLinearEquiv U P Q c hc M W (Q.sectionsEquiv _ W
        (((adicUpperStar l U.hom).obj M).X.obj.map f x)) :=
      congrArg (restrictionLinearEquiv U P Q c hc M W) (Q.section_restriction _ f x).symm
    _ = _ := restrictionLinearEquiv_apply U P Q c hc M W _
    _ = _ := congrArg (P.sectionsEquiv M
      (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj W.unop))) hh
    _ = _ := P.section_restriction M
      ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).op.map f)
      (adicComparisonPullSection U M V x)
    _ = _ := congrArg
      (((adicComparisonRestriction U P Q c).obj
        (P.E.functor.obj M)).val.map f) (restrictionLinearEquiv_apply U P Q c hc M V x).symm

include hc in
private noncomputable def restrictionObjIso (M : AdicSheaf l X) :
    Q.E.functor.obj ((adicUpperStar l U.hom).obj M) ≅
      (adicComparisonRestriction U P Q c).obj
        (P.E.functor.obj M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ (restrictionLinearEquiv U P Q c hc M V).toModuleIso) (by
      intro V W f
      apply ModuleCat.hom_ext
      ext y
      exact restrictionLinearEquiv_naturality U P Q c hc M f y))

include hc in
private noncomputable def restrictionNatIso :
    adicUpperStar l U.hom ⋙ Q.E.functor ≅
      P.E.functor ⋙ adicComparisonRestriction U P Q c :=
  NatIso.ofComponents (restrictionObjIso U P Q c hc) (by
    intro M N f
    apply SheafOfModules.hom_ext
    ext V y
    obtain ⟨x, rfl⟩ := (Q.sectionsEquiv _ V).surjective y
    change restrictionLinearEquiv U P Q c hc N V
      ((Q.E.functor.map ((adicUpperStar l U.hom).map f)).val.app V
        (Q.sectionsEquiv _ V x)) =
      ((adicComparisonRestriction U P Q c).map
        (P.E.functor.map f)).val.app V (restrictionLinearEquiv U P Q c hc M V
          (Q.sectionsEquiv _ V x))
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.hom.app V)
        ((upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) U.hom U.prop).hom.naturality
          f.hom)) x
    calc
      _ = restrictionLinearEquiv U P Q c hc N V (Q.sectionsEquiv _ V
          (((adicUpperStar l U.hom).map f).hom.hom.app V x)) :=
        congrArg (restrictionLinearEquiv U P Q c hc N V)
          (Q.section_map ((adicUpperStar l U.hom).map f) V x).symm
      _ = _ := restrictionLinearEquiv_apply U P Q c hc N V _
      _ = _ := congrArg (P.sectionsEquiv N
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))) hh
      _ = _ := P.section_map f
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))
        (adicComparisonPullSection U M V x)
      _ = _ := congrArg
        (((adicComparisonRestriction U P Q c).map
          (P.E.functor.map f)).val.app V) (restrictionLinearEquiv_apply U P Q c hc M V x).symm)

end

/-- The normalized native pullback is the literal sectionwise restriction.
Source: Stacks 03CE, 03EK and 0E8H, and step 1 of the parent comparison.
(blueprint: lem-sf-adic-slice-restriction).

Proof: conjugate the actual inverse-image/localization section isomorphism
by the two supplied additive section equivalences. The scalar-linearity
lemma makes these additive equivalences linear. Naturality on site objects
follows from the two section_restriction formulas and naturality of the actual
inverse-image comparison. This gives an objectwise sheaf-module iso. The
section_map formulas and naturality of that comparison in the native module
make these isomorphisms natural in modules. Their displayed section formula
follows from cancellation of the inverse additive section equivalence. -/
theorem adicSliceRestrictionComparison (l : ℕ) [Fact l.Prime]
    (base : ∀ X : Scheme.{u}, AdicModuleSectionComparison l X)
    (c : ∀ (X : Scheme.{u}) (U : X.ProEt),
      (base U.left).ring ≅
        (localizationRestriction RingCat.{u + 1} U.hom U.prop).obj (base X).ring)
    (hc : ∀ (X : Scheme.{u}) (U : X.ProEt) (V : U.left.ProEtᵒᵖ)
      (a : (base U.left).ring.obj.obj V), HEq (((c X U).hom.hom.app V) a) a) :
    Nonempty (AdicSliceRestrictionData l base c) := by
  refine ⟨{ sliceIso := fun X U ↦
    restrictionNatIso U (base X) (base U.left) (c X U) (hc X U), slice_sections := ?_ }⟩
  intro X U M V x
  exact restrictionLinearEquiv_apply U (base X) (base U.left) (c X U) (hc X U) M V x

end AlgebraicGeometry.ProEtale
