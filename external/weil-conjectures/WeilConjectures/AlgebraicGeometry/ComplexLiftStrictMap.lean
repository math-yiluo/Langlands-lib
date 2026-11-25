/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # ComplexLiftStrictMap

Source: Stacks Project, Tag 0BCA.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_unit_epi
    (R : Type u) [CommRing R] (I : Ideal R) (M : ModuleCat.{max u v} R) :
    Epi ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M) := by
  rw [ModuleCat.epi_iff_surjective]
  let := (Ideal.Quotient.mk I).toAlgebra
  intro x
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective R M (R ⧸ I)
    (Ideal.Quotient.mk_surjective) x
  refine ⟨y, ?_⟩
  change (1 : R ⧸ I) ⊗ₜ[R] y = x
  exact hy

set_option backward.isDefEq.respectTransparency false in
/-- Lift a reduced map into an acyclic reduced complex strictly.

Source: Stacks Project, Tag 0BCA, dotted-arrow paragraph; Derived Categories,
Tag 0649 (lifting maps from bounded-above projective complexes).
(blueprint: lem-sc-complex-lift-strict-map).

Proof: Extension of scalars preserves projectives and zero objects, so the
reduction of K is again bounded above and projective, hence K-projective.
Its map to the acyclic C is therefore homotopic to zero. For each homotopy
component, compose with the inverse of e, then apply the extension/restriction
adjunction. The quotient adjunction unit is surjective, because every scalar
modulo I comes from R and every tensor is represented by 1 tensor a vector.
Projectivity of each term of K lifts the resulting map through this unit.
Take the boundary of this lifted family, using nullHomotopicMap. Additivity
and compatibility of nullHomotopicMap with postcomposition show that its
reduction followed by e is the boundary of the original homotopy, namely the
supplied map. Acyclicity of A is not required. -/
theorem exists_complex_lift_strict_map
    (R : Type u) [CommRing R] (I : Ideal R)
    (K A : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hKbound : ∃ b : ℤ, K.IsStrictlyLE b)
    (hKproj : ∀ i : ℤ, Projective (K.X i))
    (C : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ) (hC : C.Acyclic)
    (e : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ≅ C)
    (ι : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶ C) :
    ∃ f : K ⟶ A,
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f ≫ e.hom = ι := by
  classical
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let adj := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)
  let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let := Functor.additive_of_preservesBinaryBiproducts F
  obtain ⟨b, hb⟩ := hKbound
  let := hb
  have hGb : CochainComplex.IsStrictlyLE (G.obj K) b :=
    (CochainComplex.isStrictlyLE_iff _ _).mpr
      (fun i hi ↦ F.map_isZero (K.isZero_of_isStrictlyLE b i hi))
  let := hGb
  have hGproj : ∀ i : ℤ, Projective ((G.obj K).X i) :=
    fun i ↦ adj.map_projective (K.X i) (hKproj i)
  let := hGproj
  let := CochainComplex.isKProjective_of_projective (G.obj K) b
  obtain ⟨H⟩ := CochainComplex.IsKProjective.nonempty_homotopy_zero ι hC
  have hunit : ∀ j : ℤ, Epi (adj.unit.app (A.X j)) :=
    fun j ↦ quotient_unit_epi R I (A.X j)
  let := hunit
  let := hKproj
  let α (i j : ℤ) : K.X i ⟶ A.X j :=
    Projective.factorThru
      ((adj.homEquiv (K.X i) (F.obj (A.X j))) (H.hom i j ≫ e.inv.f j))
      (adj.unit.app (A.X j))
  have hα (i j : ℤ) : F.map (α i j) ≫ e.hom.f j = H.hom i j := by
    apply (cancel_mono (e.inv.f j)).mp
    have he : e.hom.f j ≫ e.inv.f j = 𝟙 _ :=
      congrArg (fun k ↦ k.f j) e.hom_inv_id
    simp only [Category.assoc, he]
    change F.map (α i j) ≫ 𝟙 (F.obj (A.X j)) = H.hom i j ≫ e.inv.f j
    rw [Category.comp_id]
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_unit]
    change adj.unit.app (K.X i) ≫
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (α i j)) = _
    exact (adj.unit_naturality (α i j)).trans (Projective.factorThru_comp _ _)
  refine ⟨Homotopy.nullHomotopicMap α, ?_⟩
  rw [Homotopy.map_nullHomotopicMap, Homotopy.nullHomotopicMap_comp]
  have hαeq : (fun i j ↦ F.map (α i j) ≫ e.hom.f j) = H.hom := by
    funext i j
    exact hα i j
  rw [hαeq]
  apply HomologicalComplex.Hom.ext
  funext i
  simpa only [Homotopy.nullHomotopicMap, HomologicalComplex.zero_f, add_zero] using
    (H.comm i).symm


end AlgebraicGeometry
