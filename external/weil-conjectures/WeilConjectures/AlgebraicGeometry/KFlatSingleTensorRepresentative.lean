/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle

/-! # A K-flat representative for tensoring two single complexes

Source: Stacks Project, Cohomology, Tags 06YH and 06YS.
(blueprint: lem-pc-kflat-single-tensor-representative). -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 512
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- Tensoring a K-flat resolution of A with B in degree zero computes A tensor^L B.
Source: Stacks Project, Cohomology, Tags 06YH and 06YS.
(blueprint: lem-pc-kflat-single-tensor-representative).

Proof: pass P to the homotopy category and use the acyclic-tensor characterization
of categorical K-flatness. The given definition controls V tensor P; symmetry
gives P tensor V. Thus the localized tensor counit on P is invertible. Apply the
proved source QObjTensorSingleFunctorObjIso to compute Q(P) tensor B[0] as the
termwise tensorRight B complex. The augmentation a is a quasi-isomorphism, so Q(a)
and the singleFunctorIsoCompQ comparison identify Q(P) with A[0]. Tensor this
identification with B[0], then apply the source comparison and the inverse of the
single/total-tensor complex comparison. The result uses the fixed derived tensor
structure, with no alternative tensor instance. Zero factors, all integer degrees,
and unbounded P obey the same argument; no flatness condition on B is needed. -/
theorem nonempty_kFlat_single_tensor_representative
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (A B : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (a : P ⟶ (HomologicalComplex.single
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ) 0).obj A)
    (hP : CochainComplex.IsKFlatTensorResolution (R := Y.sheaf) a) :
    letI : MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
      SheafOfModules.monoidalCategory Y.sheaf
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    Nonempty (S.obj A ⊗ S.obj B ≅ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor P
        ((HomologicalComplex.single
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ) 0).obj B)
        (curriedTensor _))) := by
  classical
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  let := (SheafOfModules.tensorClosed Y.sheaf).1.some
  let := (SheafOfModules.tensorClosed Y.sheaf).2.1.some
  have : CategoryTheory.IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, u, u} _
  have (X₁ X₂ : GradedObject ℤ
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) :
      X₁.HasTensor X₂ := inferInstance
  have := schemeModule_hasFunctorialFlatResolution Y
  have hk : (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro V hV
    obtain ⟨V, rfl⟩ := V.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hV
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor V P (curriedTensor _))).2 (hP.2 V hV)
    refine ⟨?_, hr⟩
    exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso (β_ _ _) hr
  have : QuasiIso a := hP.1
  have : IsIso (DerivedCategory.Q.map a) := by infer_instance
  let e := asIso (DerivedCategory.Q.map a) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).symm.app A
  let t := DerivedCategory.QObjTensorSingleFunctorObjIso P hk B
  let s := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) B P
  exact ⟨tensorIso e.symm (Iso.refl _) ≪≫ t ≪≫ DerivedCategory.Q.mapIso s.symm⟩

end AlgebraicGeometry
