/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
@[expose] public section
universe u v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- A local homomorphism of commutative local rings reflects finite-free isomorphisms.
Source: Stacks Project, Tag 00O0, Lemma 10.79.4(3), adapted matrix argument.

Proof: Choose finite bases of ranks m and n. Scalar extension gives the same
matrix over S. Reducing the extended inverse modulo the maximal ideal of S
shows m = n, by dimension over its nonzero residue field. The determinant of
the square extended matrix is a unit, since determinants multiply and its
inverse matrix has determinant inverse to it. A local ring homomorphism
reflects units, so the original determinant is a unit in R. Multiplying the
adjugate by its inverse gives a two-sided inverse of the original matrix.
Transport this inverse through the chosen bases to obtain an inverse of φ.
The argument includes rank zero (empty determinant 1); unequal ranks cannot
satisfy the premise. No flatness is required.
(blueprint: lem-sc-local-free-base-change-reflects-iso) -/
theorem isIso_of_isIso_extendScalars_of_finite_free
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    {M N : ModuleCat R} [Module.Free R M] [Module.Finite R M]
    [Module.Free R N] [Module.Finite R N] (φ : M ⟶ N)
    (hφ : IsIso ((ModuleCat.extendScalars f).map φ)) : IsIso φ := by
  classical
  algebraize [f]
  rw [ConcreteCategory.isIso_iff_bijective] at hφ ⊢
  have h : Function.Bijective (φ.hom.baseChange S) := hφ
  let e := LinearEquiv.ofBijective (φ.hom.baseChange S) h
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  let eι := ((Algebra.TensorProduct.basis S bM).map e).indexEquiv
    (Algebra.TensorProduct.basis S bN)
  let bN' := bN.reindex eι.symm
  let cM := Algebra.TensorProduct.basis S bM
  let cN := Algebra.TensorProduct.basis S bN'
  let A := LinearMap.toMatrix bM bN' φ.hom
  have hA : LinearMap.toMatrix cM cN (φ.hom.baseChange S) =
      A.map (algebraMap R S) := LinearMap.toMatrix_baseChange S φ.hom bM bN'
  have hmul : A.map (algebraMap R S) *
      LinearMap.toMatrix cN cM e.symm.toLinearMap = 1 := by
    rw [← hA, ← LinearMap.toMatrix_comp]
    have he : (φ.hom.baseChange S).comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply x
    rw [he, LinearMap.toMatrix_id]
  have hdetS : IsUnit ((A.map (algebraMap R S)).det) :=
    Matrix.isUnit_det_of_right_inverse hmul
  have hdet : IsUnit A.det := by
    apply (isUnit_map_iff (algebraMap R S) A.det).mp
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hdetS
  let ψ := Matrix.toLin bN' bM A⁻¹
  have hleft : ψ.comp φ.hom = LinearMap.id := by
    apply (LinearMap.toMatrix bM bM).injective
    rw [LinearMap.toMatrix_comp bM bN' bM, LinearMap.toMatrix_id]
    change (LinearMap.toMatrix bN' bM) (Matrix.toLin bN' bM A⁻¹) * A = 1
    rw [LinearMap.toMatrix_toLin]
    exact Matrix.nonsing_inv_mul A hdet
  have hright : φ.hom.comp ψ = LinearMap.id := by
    apply (LinearMap.toMatrix bN' bN').injective
    rw [LinearMap.toMatrix_comp bN' bM bN', LinearMap.toMatrix_id]
    change A * (LinearMap.toMatrix bN' bM) (Matrix.toLin bN' bM A⁻¹) = 1
    rw [LinearMap.toMatrix_toLin]
    exact Matrix.mul_nonsing_inv A hdet
  exact ⟨Function.HasLeftInverse.injective ⟨ψ, LinearMap.congr_fun hleft⟩,
    Function.HasRightInverse.surjective ⟨ψ, LinearMap.congr_fun hright⟩⟩
end AlgebraicGeometry.Scheme.Modules
