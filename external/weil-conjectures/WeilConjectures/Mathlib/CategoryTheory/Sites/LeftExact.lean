/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Left exactness of the plus construction over an AB5 category

`Mathlib.CategoryTheory.Sites.LeftExact` proves that the plus construction
`J.plusFunctor D` preserves finite limits when `D` is a concrete category whose forgetful
functor preserves the filtered colimits indexed by the covers: concreteness is used only to
produce the interchange isomorphism `colimitLimitIso`, which compares a colimit over
`(J.Cover X)ᵒᵖ` with a limit of the shape being preserved.

That interchange isomorphism is available as soon as the colimit functor
`colim : ((J.Cover X)ᵒᵖ ⥤ D) ⥤ D` preserves limits of the given shape — which for a finite
shape is exactly axiom AB5 for `D`. This file redoes the argument with that hypothesis in
place of concreteness, so that the plus construction is left exact over any Grothendieck
abelian category (`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor'`,
`CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification'`).

## Main results

* `CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_plusFunctor'`: the plus
  construction preserves `K`-shaped limits whenever the colimits over the covers do.
* `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_plusFunctor'`: the plus
  construction is left exact over an AB5 category.
* `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_sheafification'`: consequently
  `J.sheafification D = J.plusFunctor D ⋙ J.plusFunctor D` is left exact.

The proofs of the first result are those of `Mathlib.CategoryTheory.Sites.LeftExact`, with
the concreteness hypotheses removed; they should replace the ones there once the Mathlib
statements are generalized.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe s t w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

noncomputable section

namespace CategoryTheory.GrothendieckTopology

variable {D : Type w} [Category.{t} D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary definition to be used in the proof that `J.plusFunctor D` commutes
with finite limits. -/
def liftToPlusObjLimitObj' {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    [∀ X : C, PreservesLimitsOfShape K (colim (J := (J.Cover X)ᵒᵖ) (C := D))]
    (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.pt ⟶ (J.plusObj (limit F)).obj (op X) :=
  let F' := F ⋙ J.diagramFunctor D X
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit F)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        refine colimit.hom_ext (fun w => ?_)
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagramFunctor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagramFunctor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagramFunctor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plusFunctor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
theorem liftToPlusObjLimitObj'_fac {K : Type s} [SmallCategory K] [HasLimitsOfShape K D]
    [∀ X : C, PreservesLimitsOfShape K (colim (J := (J.Cover X)ᵒᵖ) (C := D))]
    (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj' F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k := by
  dsimp only [liftToPlusObjLimitObj']
  rw [← (limit.isLimit (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    Category.assoc]
  congr 1
  dsimp
  rw [Category.assoc, Category.assoc, ← Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.inv_comp_eq]
  refine colimit.hom_ext (fun j => ?_)
  dsimp [plusMap]
  simp only [HasColimit.ι_isoOfNatIso_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π, Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance preservesLimitsOfShape_plusFunctor'
    (K : Type t) [SmallCategory K] [HasLimitsOfShape K D]
    [∀ X : C, PreservesLimitsOfShape K (colim (J := (J.Cover X)ᵒᵖ) (C := D))] :
    PreservesLimitsOfShape K (J.plusFunctor D) := by
  constructor; intro F; apply preservesLimit_of_evaluation; intro X
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
  refine ⟨fun S => liftToPlusObjLimitObj' F X.unop S, ?_, ?_⟩
  · intro S k
    apply liftToPlusObjLimitObj'_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj']
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    refine limit.hom_ext (fun k => ?_)
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    refine colimit.hom_ext (fun k => ?_)
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    conv_lhs => dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [colimitObjIsoColimitCompEvaluation_ι_app_hom]
    conv_lhs =>
      dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc, ← NatTrans.comp_app, limit.lift_π]
    rfl

/-- The plus construction is left exact as soon as the colimits over the covers are exact,
i.e. for any target satisfying axiom AB5. This generalizes
`CategoryTheory.GrothendieckTopology.preserveFiniteLimits_plusFunctor`, which assumes the
target concrete. -/
instance preservesFiniteLimits_plusFunctor' [HasFiniteLimits D]
    [∀ X : C, HasExactColimitsOfShape (J.Cover X)ᵒᵖ D] :
    PreservesFiniteLimits (J.plusFunctor D) := by
  have (X : C) : PreservesFiniteLimits (colim (J := (J.Cover X)ᵒᵖ) (C := D)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{t}
  intro K _ _
  apply preservesLimitsOfShape_plusFunctor'

/-- Sheafification is the plus construction applied twice, so it too is left exact over a
target satisfying axiom AB5. -/
instance preservesFiniteLimits_sheafification' [HasFiniteLimits D]
    [∀ X : C, HasExactColimitsOfShape (J.Cover X)ᵒᵖ D] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.comp_preservesFiniteLimits _ _

section IsGrothendieckAbelian

/-- Over a Grothendieck abelian category whose filtered colimits have the size of the
sieves of the site, the plus construction is left exact: axiom AB5 for `A` is exactness of
the colimits over `(J.Cover X)ᵒᵖ`. -/
instance preservesFiniteLimits_plusFunctor_of_isGrothendieckAbelian (A : Type w)
    [Category.{t} A] [Abelian A] [IsGrothendieckAbelian.{max u v} A] :
    PreservesFiniteLimits (J.plusFunctor A) :=
  inferInstance

/-- Over a Grothendieck abelian category whose filtered colimits have the size of the
sieves of the site, the two-step plus construction is left exact. -/
instance preservesFiniteLimits_sheafification_of_isGrothendieckAbelian (A : Type w)
    [Category.{t} A] [Abelian A] [IsGrothendieckAbelian.{max u v} A] :
    PreservesFiniteLimits (J.sheafification A) :=
  inferInstance

end IsGrothendieckAbelian

end CategoryTheory.GrothendieckTopology

end

end

namespace CategoryTheory

/-- **Sheafification of presheaves of sets commutes with finite limits.** For a site `C`, the
sheafification functor from presheaves of sets to sheaves of sets preserves finite limits; in
particular it sends the terminal presheaf to the terminal sheaf and binary products (computed
sectionwise) to binary products. (blueprint: `situation-conventions`) -/
theorem preservesFiniteLimits_presheafToSheaf_type {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Limits.PreservesFiniteLimits (presheafToSheaf J (Type (max u v))) :=
  inferInstance

end CategoryTheory
