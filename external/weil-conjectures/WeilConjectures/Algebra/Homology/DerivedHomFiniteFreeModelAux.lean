/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import WeilConjectures.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Algebra.Homology.HomComplexMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- The bounded-above finite-free Hom complex computes derived internal Hom when the
second complex is bounded below. This is the injective-resolution and acyclic-Hom
part of `derivedInternalHom_of_boundedAbove_finiteFree`.
Source: Stacks Project, Cohomology, Tag 0GM8, case (2), and Section 08J7
(blueprint: lem-sc-derived-hom-finite-free-model-aux).
Proof: replace `G` by a bounded-below K-injective resolution `I`; the cone of the
replacement is bounded below and acyclic, so finite-free Hom preserves the
quasi-isomorphism. The derived internal Hom computation with `I` and the
K-injective comparison then identify the localized Hom complex with derived Hom.
-/
theorem derivedInternalHom_of_boundedAbove_finiteFree_aux
    (U : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U))]
    (E G : CochainComplex (SheafOfModules.{u} (moduleRings U)) ℤ)
    (hEbounded : ∃ N : ℤ, ∀ p : ℤ, N < p → IsZero (E.X p))
    (hEfree : ∀ p : ℤ, ∃ r : ℕ, Nonempty (E.X p ≅
      SheafOfModules.free (R := moduleRings U) (ULift.{u} (Fin r))))
    (hGbounded : ∃ M : ℤ, ∀ q : ℤ, q < M → IsZero (G.X q)) :
    Nonempty (DerivedCategory.Q.obj (CategoryTheory.homComplex (R := U.sheaf) E G) ≅
      (CategoryTheory.derivedInternalHom (Opens.grothendieckTopology U) U.sheaf).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj G)) := by
  obtain ⟨M, hM⟩ := hGbounded
  have hG : G.IsStrictlyGE M := (G.isStrictlyGE_iff M).mpr hM
  obtain ⟨I, i, hi, ⟨N, hN⟩, _, hI⟩ :=
    SheafOfModules.exists_boundedBelow_injective_resolution
      (Opens.grothendieckTopology U) U.sheaf G ⟨M, hG⟩
  have : QuasiIso i := hi
  have : I.IsKInjective := hI
  have hcone : (CochainComplex.mappingCone i).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic i).mp hi
  have hconebounded : ∃ L : ℤ, ∀ q : ℤ,
      q < L → IsZero ((CochainComplex.mappingCone i).X q) := by
    refine ⟨min (M - 1) N, ?_⟩
    intro q hq
    apply (CochainComplex.mappingCone.isZero_X_iff i q).mpr
    exact ⟨hM (q + 1) (by omega),
      (I.isStrictlyGE_iff N).mp hN q (by omega)⟩
  have hHom := CochainComplex.acyclic_homComplex_of_boundedAbove_finiteFree
    E (CochainComplex.mappingCone i) hEbounded hEfree hconebounded hcone
  let f := ((CategoryTheory.homComplexFunctor (R := U.sheaf)).obj (op E)).map i
  obtain ⟨econe⟩ := CategoryTheory.homComplex_mappingCone_iso
    (Opens.grothendieckTopology U) U.sheaf E G I i
  have hf : QuasiIso f := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic f).mpr
    intro n
    exact (hHom n).of_iso econe.symm
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr hf
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).mpr hi
  obtain ⟨e⟩ := CategoryTheory.derivedInternalHom_obj_iso
    (Opens.grothendieckTopology U) U.sheaf
    (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj G) E I
    (Iso.refl _) (asIso (DerivedCategory.Q.map i)).symm
  exact ⟨asIso (DerivedCategory.Q.map f) ≪≫ e.symm⟩

end AlgebraicGeometry
