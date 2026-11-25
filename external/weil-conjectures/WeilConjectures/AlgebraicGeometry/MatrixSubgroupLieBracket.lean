/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.MixedCommutatorTangent

/-!
# Tangent matrices and the differential of a rational representation

Source: Milne, Algebraic Groups (2017), Chapter 10, Lie algebra of a closed matrix subgroup
and differential of a representation (blueprint: `def-wf-lie-algebra-derivation`).
-/

@[expose] public section

universe u

open CategoryTheory

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

/-- The matrices `X` for which `1 + εX` belongs to a closed matrix subgroup form a linear
subspace closed under commutators. Every rational representation has a linear differential
on this subspace, characterized by its dual-number points, preserving the commutator.
Source: Milne, Algebraic Groups (2017), Chapter 10
(blueprint: `def-wf-lie-algebra-derivation`).

Proof: the subspace is the matrix Lie algebra `lieSubalgebra I`. The differential of the closed
immersion `V(I) ⟶ GL_n` identifies `Lie(V(I))` with it, and the differential of `r` is read
through this identification. A point `g` with matrix `1 + εX` reduces to the identity, so it is
the tangent point of the tangent vector with matrix `X`, and `r(g) = 1 + ε dr(X)`. Both
differentials are homomorphisms of Lie algebras, so `dr` preserves `XY - YX`.

Finite-dimensional vector spaces are written in coordinates `kⁿ` and `kᵐ`; neither index
set is required to be nonempty. The final equality uses any `Z` representing `[X,Y]` in the
subspace. -/
theorem exists_tangentMatrixSubmodule_differential
    {k : Type u} [Field k]
    {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (I : Ideal (Matrix.GeneralLinearGroup.CoordinateRing n k)) [I.IsHopfIdeal k] :
    ∃ S : Submodule k (Matrix n n k),
      (∀ X : Matrix n n k, X ∈ S ↔
        dualUnit X ∈ Matrix.GeneralLinearGroup.zeroLocus I (DualNumber k)) ∧
      (∀ X ∈ S, ∀ Y ∈ S, X * Y - Y * X ∈ S) ∧
      (∀ (r : RationalHom (subgroupScheme I) m) [IsMonHom r],
        ∃ d : S →ₗ[k] Matrix m m k,
          (∀ (X : S) (g : AlgebraicGeometry.points (subgroupScheme I) (DualNumber k)),
            homMulEquiv n k (DualNumber k) (g ≫ subgroupSchemeι I) = dualUnit X.val →
              r.points (DualNumber k) g = dualUnit (d X)) ∧
          (∀ X Y Z : S, Z.val = X.val * Y.val - Y.val * X.val →
            d Z = d X * d Y - d Y * d X)) := by
  set ι := RationalHom.differential (subgroupSchemeι I)
  let S := (lieSubalgebra I).toSubmodule
  let e : GrpObj.Lie (subgroupScheme I) ≃ₗ[k] S := LinearEquiv.ofBijective
    (LinearMap.codRestrict S ι.toLinearMap differential_subgroupSchemeι_mem)
    ⟨fun x y h ↦ differential_subgroupSchemeι_injective (congrArg Subtype.val h),
      fun X ↦ (exists_differential_subgroupSchemeι_eq X.2).imp fun _ h ↦ Subtype.ext h⟩
  have he (x : GrpObj.Lie (subgroupScheme I)) : (e x : Matrix n n k) = ι x := rfl
  have : IsSubgroupScheme (subgroupSchemeι I) := IsSubgroupScheme.of_mono _
  refine ⟨S, fun _ ↦ mem_lieSubalgebra, fun X hX Y hY ↦ ?_, fun r _ ↦
    ⟨r.differential.toLinearMap ∘ₗ e.symm.toLinearMap, fun X g hg ↦ ?_, fun X Y Z hZ ↦ ?_⟩⟩
  · rw [← Ring.lie_def]
    exact (lieSubalgebra I).lie_mem hX hY
  · obtain ⟨x, rfl⟩ := GrpObj.exists_tangentPoint_eq
      (mem_tangentGroup_of_homMulEquiv_comp_eq_dualUnit _ hg)
    have hx : e x = X := Subtype.ext (dualUnit_injective (by
      rw [he, ← RationalHom.points_tangentPoint, RationalHom.points_apply, hg]))
    rw [RationalHom.points_tangentPoint, LinearMap.comp_apply, ← hx]
    simp
  · obtain ⟨x, rfl⟩ := e.surjective X
    obtain ⟨y, rfl⟩ := e.surjective Y
    have hz : Z = e ⁅x, y⁆ := Subtype.ext (by rw [hZ, he, he, he, LieHom.map_lie, Ring.lie_def])
    simp only [hz, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LieHom.coe_toLinearMap, LieHom.map_lie, Ring.lie_def]

end AlgebraicGeometry.GeneralLinearGroup
