/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsTruncationIso
import WeilConjectures.AlgebraicGeometry.AffineDerivedSectionsTruncatedBottom

/-! # Cohomology of derived affine sections

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: lem-pc-affine-derived-sections-homology-comparison).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Derived affine sections commute naturally with cohomology on D_QCoh.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, cohomology calculation.
(blueprint: lem-pc-affine-derived-sections-homology-comparison).

Proof: Global sections is right adjoint to tilde, so preserves products. Scalar
transport through ΓSpecIso is exact and preserves products. Affine vanishing gives
the uniform bound N = 1 on quasi-coherent modules; the exact conservative forgetful
functor to abelian groups detects the resulting cohomology isomorphisms. For each
shift of K, apply the unbounded cohomological bound to its strictly negative
truncation. Derived sections of that truncation vanish in degrees zero and one.
The truncation triangle thus identifies degree-zero derived sections of K with
those of its nonnegative truncation. Left exactness identifies the latter with
ordinary sections of H^0(K). All truncation maps are natural, so shifting gives
a natural isomorphism in every degree. Transport along hG to obtain the displayed
comparison. No boundedness hypothesis or nonzero-ring hypothesis is needed. -/
theorem affineDerivedSections_homology_comparison (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (n : ℤ) :
    Nonempty (G ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n ⋙
        moduleSpecΓFunctor (R := .of A)) := by
  let S := (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let ι := (schemeDerivedQCohProperty (Spec (.of A))).ι
  let τ := Functor.whiskerLeft ι
    (Functor.whiskerRight (Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncGEπ n) S) H)
  have (K : schemeDerivedQCohCategory (Spec (.of A))) : IsIso (τ.app K) :=
    affineDerivedSections_truncGE_isIso A K n
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  obtain ⟨eG⟩ := hG
  obtain ⟨eB⟩ := affineDerivedSections_truncated_bottom A n
  exact ⟨Functor.isoWhiskerRight eG H ≪≫ asIso τ ≪≫
    Functor.isoWhiskerLeft ι eB⟩

end AlgebraicGeometry
