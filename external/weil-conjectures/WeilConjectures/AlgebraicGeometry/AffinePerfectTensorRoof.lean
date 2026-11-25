/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart
import WeilConjectures.AlgebraicGeometry.AffineKoszulSectionRoof
import WeilConjectures.AlgebraicGeometry.TensorRoofTransposition

/-! # Koszul tensor roof lifting an affine open morphism

Source: Stacks Project, Tag 08EH, construction of the two maps in Lemma 36.13.7
(blueprint: lem-sc-affine-perfect-tensor-roof).
-/

@[expose] public section

set_option autoImplicit false

universe uX wD

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
-- Keep tensor instances as local abbreviations during the representative computation.
private theorem affinePerfectTensorRoof_aux
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    let := SheafOfModules.monoidalCategory X.sheaf
    let := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ := by
  classical
  -- Reuse the tensor instances bound in the conclusion instead of elaborating them again.
  intro monoidal monoidalPreadditive
  let H := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf).obj (Opposite.op A, E'.obj)
  have hH : schemeDerivedQCohProperty X H :=
    rhom_supported_quasiCoherent_perfect_part X A E'.obj E'.property hA
  obtain ⟨e, he⟩ := tensor_roof_transposition X U A E'.obj P hP eA
  obtain ⟨J, hJ, hperfect, u, ξ, hu, hξ⟩ :=
    affine_koszul_section_roof X U hU ⟨H, hH⟩ (e.symm α)
  obtain ⟨γ, hβ, hγ⟩ := he J hJ u hu ξ (e.symm α) hξ
  -- Infer the augmentation from its isomorphism proof, avoiding a second tensor computation.
  refine ⟨J, hJ, hperfect, u, γ, @asIso _ _ _ _ _ hβ, rfl, ?_⟩
  apply (Iso.eq_inv_comp _).2
  simpa only [asIso_hom, Equiv.apply_symm_apply] using hγ

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
/-- Construct the Koszul roof and the lifted map for a fixed K-flat model of the source.
This statement does not assert perfectness or support of the total tensor.
Source: Stacks Project, Tag 08EH, proof of Lemma 36.13.7
(blueprint: lem-sc-affine-perfect-tensor-roof).

Proof:
1. RHom(A,E') is quasi-coherent for perfect A and arbitrary quasi-coherent E'.
   Restriction of RHom and its zeroth global sections identify alpha with a section
   of this RHom object on U. Transport along X's canonical affine isomorphism to
   Spec of its global sections and choose a finite principal-open cover of U.
2. Apply affine_perfect_open_represent_cohomology to the RHom object. Surjectivity
   of its filtered-colimit cocone gives a Koszul tail and a map into RHom representing
   this section. The tail is perfect and its augmentation is invertible on U.
3. Take J to be the associated-sheaf Koszul tail, transported back along the affine
   isomorphism. It is bounded finite locally free, hence K-flat by the bounded-above
   flat criterion, and has its canonical chain augmentation u to the tensor unit.
   Transpose the representing map under derived tensor-Hom, computed on P and J,
   to obtain gamma. Tensor u with id_P, then follow by the right unitor and eA.
4. Restriction commutes with the representative tensor and RHom. Its tensor
   augmentation is therefore an isomorphism. Naturality of transposition shows
   gamma restricted, precomposed with its inverse, is precisely alpha. Transport
   back from Spec. Empty U gives the zero tail and zero map; no nonempty-open
   assumption is used. -/
theorem exists_affine_perfect_tensor_roof
    (X : Scheme.{uX}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{wD} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))]
    (E' : schemeDerivedQCohCategory X) (A : schemeDerivedCategory X) (hA : IsPerfect X A)
    (α : ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj A ⟶
        ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj)
    (P : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eA : DerivedCategory.Q.obj P ≅ A) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    ∃ J : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := X.sheaf) J ∧ IsPerfect X (DerivedCategory.Q.obj J) ∧
      ∃ u : J ⟶ HomologicalComplex.tensorUnit
          (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ),
        let B := DerivedCategory.Q.obj (CochainComplex.mapBifunctor P J (curriedTensor _))
        let β : B ⟶ A := DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap (𝟙 P) u (curriedTensor _) (ComplexShape.up ℤ)) ≫
          DerivedCategory.Q.map (HomologicalComplex.rightUnitor P).hom ≫ eA.hom
        let R := ((SheafOfModules.overFunctor.{uX} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{uX} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory
        ∃ (γ : B ⟶ E'.obj) (bU : R.obj B ≅ R.obj A),
          bU.hom = R.map β ∧ α = bU.inv ≫ R.map γ := by
  exact affinePerfectTensorRoof_aux X U hU E' A hA α P hP eA

end AlgebraicGeometry.Scheme
