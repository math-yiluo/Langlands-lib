/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineModelComparisonData
public import WeilConjectures.AlgebraicGeometry.AffineModelCoherentObjectComparisons

/-! # Constructor interface for affine comparison data
Source: the explicit comparison-data formula, Stacks Project, Tag 09RE.
(blueprint: lem-pc-affine-model-comparison-data-from-hom-equations). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Constructor API for the original comparison predicate, with canonical functor maps.
Source: the explicit defining formula of affineModelComparisonData.
(blueprint: lem-pc-affine-model-comparison-data-from-hom-equations).

Proof: Expand the explicit proposition affineModelComparisonData. Use the supplied
coordinate equivalences d and dlim and the supplied object comparisons as its six
existential witnesses. The two remaining goals are precisely hstage and hlim:
the map equation for affineModelLocalizedTilde is d.functor.map applied to Q.map
of termwise tilde, and affineModelTildeComplex is the original explicit termwise
tilde functor. The scalarExtensionHom and perfectStageMap/perfectLimitMap terms
are the same after expanding the named stage and limit arrows.
Proof irrelevance identifies the generated preorder and HasPullback
proof constants with the direct instances. No mathematical choice or new geometric
assertion is needed. Identity arrows, zero models and zero rings are included. -/
theorem affineModelComparisonData_of_hom_equations
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (βE : AffineModelLimitObject R c i Y s P F C E dlim)
    (βK : AffineModelLimitObject R c i Y s Q F C K dlim)
    (hstage : ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      (αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
          (F.map (homOfLE k.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk)))
          E K a) ≫ (αK k).hom =
      perfectStageMap R s j.val.property hjk
        ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom))
    (hlim : ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
          (C.ι.app ⟨i, le_rfl⟩).hom
          (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ βK.hom =
      perfectLimitMap R c s j.val.property
        ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom)) :
    affineModelComparisonData R c i Y s P Q F C E K := by
  delta affineModelComparisonData
  refine ⟨d, dlim, αE, αK, βE, βK, ?_, ?_⟩
  · intro j k hjk a
    exact hstage j k hjk a
  · intro j a
    exact hlim j a

end AlgebraicGeometry
