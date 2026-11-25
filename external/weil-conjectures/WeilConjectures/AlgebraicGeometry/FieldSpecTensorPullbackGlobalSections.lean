/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.Topology.PointModuleEvaluationEquivalence

/-! # Global sections of tensor pullback between field spectra

Source: Stacks Project, Tags 01I9 and 009A.
(blueprint: lem-sc-field-spec-tensor-pullback-global-sections).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- On field spectra tensor pullback becomes extension of scalars on global sections.
Source: Stacks Project, Tags 01I9 and 009A.
(blueprint: lem-sc-field-spec-tensor-pullback-global-sections).

Proof: evaluation is an equivalence on the one-point spectrum of a field. Transporting
scalars along GammaSpecIso is also an equivalence, so the tilde-global-sections
adjunction is an equivalence. Precompose with tilde. The tensor-pullback comparison
for tilde identifies this composite with extension of scalars followed by tilde.
The tilde-global-sections unit cancels tilde on both sides. Full faithfulness of
precomposition by the tilde equivalence lifts this natural isomorphism back to all
module sheaves. No quasi-coherence hypothesis is needed on a one-point field spectrum;
the zero module and arbitrary field extensions are included. -/
theorem nonempty_fieldSpec_tensorPullback_globalSections_iso
    (K L : Type u) [Field K] [Field L] (f : CommRingCat.of K ⟶ CommRingCat.of L) :
    Nonempty
      (Scheme.Modules.tensorPullback (Spec.map f) ⋙
          (SheafOfModules.evaluation
            (moduleRings (Spec (CommRingCat.of L)).toRingedSpace) (op ⊤) ⋙
              ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom) ≅
        (SheafOfModules.evaluation
            (moduleRings (Spec (CommRingCat.of K)).toRingedSpace) (op ⊤) ⋙
              ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) ⋙
          ModuleCat.extendScalars f.hom) := by
  have : (RingedSpace.globalSectionsFunctor
      (Spec (CommRingCat.of K)).toRingedSpace).IsEquivalence :=
    RingedSpace.globalSectionsFunctor_isEquivalence_of_unique _
  have : (ModuleCat.restrictScalars
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have : (moduleSpecΓFunctor (R := CommRingCat.of K)).IsEquivalence :=
    inferInstanceAs ((RingedSpace.globalSectionsFunctor
      (Spec (CommRingCat.of K)).toRingedSpace ⋙
        ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).IsEquivalence)
  have : (tilde.functor (CommRingCat.of K)).IsEquivalence :=
    tilde.adjunction.isEquivalence_left_of_isEquivalence_right
  obtain ⟨e, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso f
  let d : tilde.functor (CommRingCat.of K) ⋙
      (Scheme.Modules.tensorPullback (Spec.map f) ⋙ moduleSpecΓFunctor (R := CommRingCat.of L)) ≅
      tilde.functor (CommRingCat.of K) ⋙
        (moduleSpecΓFunctor (R := CommRingCat.of K) ⋙ ModuleCat.extendScalars f.hom) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (tilde.toTildeΓNatIso (R := CommRingCat.of L)).symm ≪≫
      Functor.rightUnitor _ ≪≫
      (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := CommRingCat.of K)) _ ≪≫
      Functor.associator _ _ _
  exact ⟨((Functor.whiskeringLeft _ _ _).obj
    (tilde.functor (CommRingCat.of K))).preimageIso d⟩

end AlgebraicGeometry
