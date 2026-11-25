/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexLimits

/-!
# Exact colimits and quasi-isomorphisms

Supplement to `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
noncomputable def functorEquivalenceInverseCompMapHomologicalComplexColim
    (C : Type*) [Category* C] [HasZeroMorphisms C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category* J] [HasColimitsOfShape J C] :
    (functorEquivalence C c J).inverse ⋙ colim.mapHomologicalComplex c ≅ colim :=
  NatIso.ofComponents (fun F ↦
    (Hom.isoOfComponents (fun i ↦ IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitOfPreserves (eval C c i) (colimit.isColimit F))) (by aesop_cat))) (by
          intro F G f
          ext i
          dsimp
          ext j
          simp [← comp_f])

set_option backward.defeqAttrib.useBackward true in
lemma quasiIso_functorCategory_iff {C : Type*} [Category* C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category* J]
    {K L : HomologicalComplex (J ⥤ C) c} (f : K ⟶ L) :
    QuasiIso f ↔
      ∀ (j : J), QuasiIso ((((evaluation J C).obj j).mapHomologicalComplex c).map f) := by
  constructor
  · intro _ j
    infer_instance
  · intro h
    constructor
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, NatTrans.isIso_iff_isIso_app]
    intro j
    apply ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (((evaluation J C).obj j).mapHomologicalComplexHomologyIso c i)).app f)).1
    dsimp
    simp only [MorphismProperty.isomorphisms.iff]
    infer_instance

set_option backward.defeqAttrib.useBackward true in
instance isStableUnderColimitsOfShape_quasiIso
    (C : Type*) [Category* C] [Abelian C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category* J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    (HomologicalComplex.quasiIso C c).IsStableUnderColimitsOfShape J := by
  suffices ∀ ⦃F₁ F₂ : J ⥤ HomologicalComplex C c⦄ (f : F₁ ⟶ F₂)
    (hf : (quasiIso C c).functorCategory J f), QuasiIso (colimMap f) from
      ⟨by
        intro F₁ F₂ c₁ c₂ h₁ h₂ f hf φ hφ
        refine ((quasiIso C c).arrow_mk_iso_iff
          (Arrow.isoMk (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₁)
            (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h₂)
            (colimit.hom_ext (by aesop)))).1 (this f hf)⟩
  intro F₁ F₂ f hf
  have : QuasiIso ((functorEquivalence.inverse C c J).map f) := by
    rwa [quasiIso_functorCategory_iff]
  refine ((quasiIso C c).arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso
    ((functorEquivalenceInverseCompMapHomologicalComplexColim C c J))).app (Arrow.mk f))).1 ?_
  dsimp
  simp only [mem_quasiIso_iff]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
lemma isStableUnderColimitsOfShape_preservesQuasiIso
    (C₁ C₂ : Type*) [Category* C₁] [Abelian C₁] [Category* C₂] [Abelian C₂]
    {ι₁ ι₂ : Type*} (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂)
    (J : Type*) [Category* J]
    [HasColimitsOfShape J C₂] [HasExactColimitsOfShape J C₂] :
    (preservesQuasiIso (C₁ := C₁) (C₂ := C₂)
      (c₁ := c₁) (c₂ := c₂)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro G ⟨p⟩ K₁ L₁ f hf
    simp only [MorphismProperty.inverseImage_iff]
    let hcK := isColimitOfPreserves ((evaluation _ _).obj K₁) p.isColimit
    let hcL := isColimitOfPreserves ((evaluation _ _).obj L₁) p.isColimit
    exact MorphismProperty.colimitsOfShape_le _
      (MorphismProperty.colimitsOfShape.mk' _ _ _ _ hcK hcL
      ((Functor.whiskerLeft p.diag ((evaluation _ _).map f)))
      (fun j ↦ p.prop_diag_obj j _ hf) _ (fun j ↦ by simp))

end HomologicalComplex
