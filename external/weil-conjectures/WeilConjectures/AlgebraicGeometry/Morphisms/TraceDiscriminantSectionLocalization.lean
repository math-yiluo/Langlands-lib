/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionIdeal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatAffineBasis
import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionGermGenerator

/-!
# Localization of the explicit discriminant section ideal

## References

* Stacks Project, Tag 0BVH, construction before Lemma 49.3.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem basis_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (_b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (r : Γ(Y, U.1)),
      letI := (f.app (Y.basicOpen r)).hom.toAlgebra
      Nonempty (Module.Basis (Fin n) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := by
  let := (f.app U.1).hom.toAlgebra
  intro n b r
  let A := Γ(Y, U.1)
  let B := Γ(X, f ⁻¹ᵁ U.1)
  let Ar := Γ(Y, Y.basicOpen r)
  let Br := Γ(X, f ⁻¹ᵁ Y.basicOpen r)
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra A Ar :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Ar := U.2.isLocalization_basicOpen r
  let : Algebra B Br := (X.presheaf.map
    (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away (algebraMap A B r) Br :=
    (U.2.preimage f).isLocalization_of_eq_basicOpen (algebraMap A B r) _
      (Scheme.preimage_basicOpen f r)
  let : Algebra A Br := ((algebraMap B Br).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Br := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Ar Br := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (f.naturality (homOfLE (Y.basicOpen_le r)).op)) a).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers r)) Br := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap A B r) Br)
  exact ⟨b.localizationLocalization Ar (.powers r) Br⟩

private theorem exists_affine_basis_le
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    ∃ V : Y.affineOpens, V.1 ≤ U.1 ∧ y ∈ V.1 ∧
      (letI := (f.app V.1).hom.toAlgebra
       ∃ n : ℕ, Nonempty (Module.Basis (Fin n) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1))) := by
  obtain ⟨W, hyW, n, ⟨b⟩⟩ := exists_affine_basis_of_finite_flat f y
  obtain ⟨r, s, hrs, hyr⟩ :=
    exists_basicOpen_le_affine_inter W.2 U.2 y ⟨hyW, hy⟩
  refine ⟨Y.affineBasicOpen r, hrs.trans_le (Y.basicOpen_le s), hyr, n, ?_⟩
  exact basis_basicOpen f W n b r

private theorem sectionIdeal_map_germ_eq
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U V : Y.affineOpens)
    (h : V.1 ≤ U.1) (y : Y) (hy : y ∈ V.1) :
    letI := (f.app V.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)),
      (traceDiscriminantSectionIdeal f U).map (Y.presheaf.germ U.1 y (h hy)).hom =
        (Ideal.span {Algebra.discr Γ(Y, V.1) b}).map (Y.presheaf.germ V.1 y hy).hom := by
  let := (f.app V.1).hom.toAlgebra
  intro n b
  apply le_antisymm
  · have hUV : traceDiscriminantSectionIdeal f U ≤
        (Ideal.span {Algebra.discr Γ(Y, V.1) b}).comap
          (Y.presheaf.map (homOfLE h).op).hom :=
      iInf_le_of_le V (iInf_le_of_le h (iInf_le_of_le n (iInf_le_of_le b le_rfl)))
    have he := Ideal.map_mono (f := (Y.presheaf.germ V.1 y hy).hom)
      (Ideal.map_le_iff_le_comap.mpr hUV)
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res] using he
  · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    exact traceDiscriminantSectionIdeal_germ_generator_mem f U V h y hy n b

/-- The explicitly defined family of discriminant section ideals localizes. -/
theorem traceDiscriminantSectionIdeal_map_basicOpen
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    (traceDiscriminantSectionIdeal f U).map
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
        traceDiscriminantSectionIdeal f (Y.affineBasicOpen r) := by
  rw [(Y.affineBasicOpen r).2.ideal_ext_iff]
  intro y hy
  obtain ⟨V, hV, hyV, n, ⟨b⟩⟩ := exists_affine_basis_le f (Y.affineBasicOpen r) y hy
  have hVU : V.1 ≤ U.1 := hV.trans (Y.basicOpen_le r)
  have hU := sectionIdeal_map_germ_eq f U V hVU y hyV n b
  have hD := sectionIdeal_map_germ_eq f (Y.affineBasicOpen r) V hV y hyV n b
  rw [Ideal.map_map]
  have hg := TopCat.Presheaf.germ_res Y.presheaf
    (homOfLE (Y.affineBasicOpen_le r)) y hy
  rw [← CommRingCat.hom_comp, hg]
  exact hU.trans hD.symm

end AlgebraicGeometry.Scheme
