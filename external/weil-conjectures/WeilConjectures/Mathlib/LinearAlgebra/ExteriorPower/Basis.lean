/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrices of exterior powers

For a matrix `A` indexed by a linearly ordered finite type `n`, the matrix of `s × s` minors
`Matrix.exteriorPower s A` is the matrix of `⋀^s A` in the exterior basis indexed by the
`s`-element subsets of `n`.  It is multiplicative, so it defines a group homomorphism
`GL n R →* GL (powersetCard n s) R`, natural in the ring `R`.

An endomorphism that is diagonal in a basis with entries `dᵢ` has, on `⋀^s`, the products
`∏_{i ∈ I} dᵢ` over the `s`-element subsets `I` as its only possible eigenvalues.

## Main declarations

* `Matrix.exteriorPower`: the matrix of `s × s` minors.
* `LinearMap.toMatrix_exteriorPower_map`: it is the matrix of `⋀^s f` in the exterior basis.
* `Matrix.GeneralLinearGroup.exteriorPower`: the induced homomorphism of general linear groups.
* `exteriorPower.exists_eq_prod_of_hasEigenvalue_map`: the eigenvalues of `⋀^s f` for `f`
  diagonal in a basis.
-/

@[expose] public section

open Module Set.powersetCard

namespace Matrix

variable {n R : Type*} [LinearOrder n] [CommRing R]

/-- The matrix of `s × s` minors of `A`: its entry at `(I, J)` is the minor of `A` with rows `I`
and columns `J`.  It is the matrix of `⋀^s A` in the exterior basis, see
`LinearMap.toMatrix_exteriorPower_map`. -/
noncomputable def exteriorPower (s : ℕ) (A : Matrix n n R) :
    Matrix (Set.powersetCard n s) (Set.powersetCard n s) R :=
  Matrix.of fun I J ↦ (A.submatrix (ofFinEmbEquiv.symm I) (ofFinEmbEquiv.symm J)).det

theorem exteriorPower_apply (s : ℕ) (A : Matrix n n R) (I J : Set.powersetCard n s) :
    A.exteriorPower s I J = (A.submatrix (ofFinEmbEquiv.symm I) (ofFinEmbEquiv.symm J)).det :=
  rfl

/-- The matrix of minors is natural in the ring of coefficients. -/
theorem exteriorPower_map {S : Type*} [CommRing S] (f : R →+* S) (s : ℕ) (A : Matrix n n R) :
    (A.map f).exteriorPower s = (A.exteriorPower s).map f := by
  ext I J
  simp [exteriorPower_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

end Matrix

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n : Type*} [Fintype n] [LinearOrder n]

/-- The matrix of `⋀^s f` in the exterior basis of a basis `b` is the matrix of `s × s` minors of
the matrix of `f`. -/
theorem toMatrix_exteriorPower_map (b : Basis n R M) (s : ℕ) (f : M →ₗ[R] M) :
    toMatrix (b.exteriorPower s) (b.exteriorPower s) (exteriorPower.map s f) =
      (toMatrix b b f).exteriorPower s := by
  ext I J
  rw [toMatrix_apply, exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMultiDual_apply_ιMulti, Matrix.exteriorPower_apply, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [toMatrix_apply]

end LinearMap

namespace Matrix

variable {n R : Type*} [Fintype n] [LinearOrder n] [CommRing R]

omit [Fintype n] in
@[simp]
theorem exteriorPower_one [Finite n] (s : ℕ) : (1 : Matrix n n R).exteriorPower s = 1 := by
  have := Fintype.ofFinite n
  rw [← LinearMap.toMatrix_id (Pi.basisFun R n), ← LinearMap.toMatrix_exteriorPower_map,
    exteriorPower.map_id, LinearMap.toMatrix_id]

theorem exteriorPower_mul (s : ℕ) (A B : Matrix n n R) :
    (A * B).exteriorPower s = A.exteriorPower s * B.exteriorPower s := by
  have h (C : Matrix n n R) : C = LinearMap.toMatrix (Pi.basisFun R n) (Pi.basisFun R n)
      (Matrix.toLin (Pi.basisFun R n) (Pi.basisFun R n) C) := by
    rw [LinearMap.toMatrix_toLin]
  rw [h (A * B), h A, h B, Matrix.toLin_mul (Pi.basisFun R n) (Pi.basisFun R n) (Pi.basisFun R n),
    ← LinearMap.toMatrix_exteriorPower_map, ← LinearMap.toMatrix_exteriorPower_map,
    ← LinearMap.toMatrix_exteriorPower_map, exteriorPower.map_comp,
    LinearMap.toMatrix_comp ((Pi.basisFun R n).exteriorPower s)
      ((Pi.basisFun R n).exteriorPower s) ((Pi.basisFun R n).exteriorPower s)]
  simp only [LinearMap.toMatrix_toLin]

/-- The matrix of minors as a monoid homomorphism. -/
@[simps]
noncomputable def exteriorPowerMonoidHom (s : ℕ) :
    Matrix n n R →* Matrix (Set.powersetCard n s) (Set.powersetCard n s) R where
  toFun := exteriorPower s
  map_one' := exteriorPower_one s
  map_mul' := exteriorPower_mul s

/-- The homomorphism `GL n R →* GL (powersetCard n s) R` induced by the `s`-th exterior power. -/
noncomputable def GeneralLinearGroup.exteriorPower (s : ℕ) :
    GL n R →* GL (Set.powersetCard n s) R :=
  Units.map (exteriorPowerMonoidHom s)

@[simp]
theorem GeneralLinearGroup.coe_exteriorPower (s : ℕ) (g : GL n R) :
    (GeneralLinearGroup.exteriorPower s g : Matrix _ _ R) = (g : Matrix n n R).exteriorPower s :=
  rfl

/-- The exterior power of general linear groups is natural in the ring of coefficients. -/
theorem GeneralLinearGroup.exteriorPower_map {S : Type*} [CommRing S] (f : R →+* S) (s : ℕ)
    (g : GL n R) :
    GeneralLinearGroup.exteriorPower s (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f (GeneralLinearGroup.exteriorPower s g) := by
  ext : 1
  simp [Matrix.exteriorPower_map]

end Matrix

namespace exteriorPower

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : Type*} [LinearOrder n]

/-- If `f` is diagonal in a basis `b`, with `f (b i) = d i • b i`, then `⋀^s f` is diagonal in the
exterior basis, with entry `∏_{i ∈ I} d i` at the subset `I`. -/
theorem map_basis_exteriorPower_of_diagonal (b : Basis n K V) {f : V →ₗ[K] V} {d : n → K}
    (hf : ∀ i, f (b i) = d i • b i) (s : ℕ) (I : Set.powersetCard n s) :
    map s f (b.exteriorPower s I) = (∏ i ∈ (I : Finset n), d i) • b.exteriorPower s I := by
  rw [basis_apply, map_apply_ιMulti_family, ιMulti_family, ιMulti_family]
  have : (⇑f ∘ ⇑b) ∘ ofFinEmbEquiv.symm I =
      fun j ↦ d (ofFinEmbEquiv.symm I j) • (⇑b ∘ ofFinEmbEquiv.symm I) j := by
    ext j
    simp [hf]
  rw [this, AlternatingMap.map_smul_univ]
  congr 1
  conv_rhs => rw [← Finset.map_orderEmbOfFin_univ (I : Finset n) I.prop, Finset.prod_map]
  rfl

/-- If `f` is diagonal in a basis `b`, with `f (b i) = d i • b i`, then every eigenvalue of `⋀^s f`
is a product `∏_{i ∈ I} d i` over an `s`-element subset `I`. -/
theorem exists_eq_prod_of_hasEigenvalue_map (b : Basis n K V) {f : V →ₗ[K] V} {d : n → K}
    (hf : ∀ i, f (b i) = d i • b i) {s : ℕ} {c : K}
    (hc : Module.End.HasEigenvalue (map s f) c) :
    ∃ I : Set.powersetCard n s, c = ∏ i ∈ (I : Finset n), d i := by
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  obtain ⟨I, hI⟩ : ∃ I, (b.exteriorPower s).repr x I ≠ 0 := by
    by_contra! h
    exact hx.2 ((b.exteriorPower s).repr.injective (by ext I; simp [h]))
  refine ⟨I, mul_right_cancel₀ hI ?_⟩
  have hdiag : map s f = (b.exteriorPower s).constr K
      fun J ↦ (∏ i ∈ (J : Finset n), d i) • b.exteriorPower s J :=
    (b.exteriorPower s).ext fun J ↦ by
      rw [Basis.constr_basis, map_basis_exteriorPower_of_diagonal b hf]
  have h := congrArg (fun y ↦ (b.exteriorPower s).repr y I) (hx.apply_eq_smul)
  rw [hdiag, Basis.constr_apply, map_finsuppSum, Finsupp.sum_apply] at h
  rw [Finsupp.sum_eq_single I] at h
  · simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at h
    rw [← h, mul_comm]
  · intro J _ hJ
    simp [hJ]
  · simp

end exteriorPower
