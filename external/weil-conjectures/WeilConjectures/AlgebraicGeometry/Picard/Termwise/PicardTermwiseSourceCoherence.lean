/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PicardTermwiseModels
public import WeilConjectures.AlgebraicGeometry.Picard.Termwise.PicardTermwiseSingleMapComposition

/-! # Coherence of the termwise source single

## References

* Stacks Project, Tags 06YJ and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

instance isIso_picardTermwiseSingleMap_unit {W T : Scheme.{v}} (t : T ⟶ W) :
    IsIso (picardTermwiseSingleMap t (SheafOfModules.unit (moduleRings W.toRingedSpace))) := by
  have : SheafOfModules.IsInvertible.{v, v, v}
      (SheafOfModules.unit (moduleRings W.toRingedSpace)) :=
    SheafOfModules.instIsInvertibleUnit (R := W.ringCatSheaf)
  have := Modules.isIso_canonicalSinglePullbackMap t
    (SheafOfModules.unit (moduleRings W.toRingedSpace))
  unfold picardTermwiseSingleMap
  infer_instance

/-- The canonical counit comparison for the source single: the derived pullback of the
degree-zero single of the structure sheaf is the single of its tensor pullback. -/
def picardTermwiseSourceIso {W T : Scheme.{v}} (t : T ⟶ W) :
    (derivedPullback t).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings W.toRingedSpace)) 0).obj
        (SheafOfModules.unit (moduleRings W.toRingedSpace))) ≅
      DerivedCategory.Q.obj (picardTermwiseSource t) :=
  asIso (picardTermwiseSingleMap t (SheafOfModules.unit (moduleRings W.toRingedSpace)))

@[simp]
theorem picardTermwiseSourceIso_hom {W T : Scheme.{v}} (t : T ⟶ W) :
    (picardTermwiseSourceIso t).hom =
      picardTermwiseSingleMap t (SheafOfModules.unit (moduleRings W.toRingedSpace)) :=
  rfl

/-- The canonical counit comparison `picardTermwiseSourceIso` for the source singles
commutes with successive pullback. This assertion concerns only the source, with no local
perfect model. -/
theorem picard_termwise_source_coherence {W T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W)
    (t' : T' ⟶ W) (ht : i ≫ t = t') :
    let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
        eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
    (picardTermwiseSourceIso t').hom ≫
        DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
      c.inv.app _ ≫ (derivedPullback i).map (picardTermwiseSourceIso t).hom ≫
        (picardTermwiseCounit i).app (picardTermwiseSource t) := by
  intro c
  have h := picardTermwiseSingleMap_composition i t t' ht
    (SheafOfModules.unit (moduleRings W.toRingedSpace))
  change c.hom.app _ ≫ (picardTermwiseSourceIso t').hom ≫
      DerivedCategory.Q.map (picardTermwiseSourceRestrictionIso i t t' ht).hom =
    (derivedPullback i).map (picardTermwiseSourceIso t).hom ≫
      (picardTermwiseCounit i).app (picardTermwiseSource t) at h
  exact (c.app _).eq_inv_comp.mpr h

end
end AlgebraicGeometry.Scheme
