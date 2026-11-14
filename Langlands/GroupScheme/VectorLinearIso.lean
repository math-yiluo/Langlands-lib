import Langlands.GroupScheme.VectorMatrixMap
import Langlands.GroupScheme.IntegralModel.ScaledVector
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Polynomial vector-group isomorphisms from linear equivalences -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.VectorGroup

variable {R : CommRingCat.{u}} {n m : ℕ}

/-- Mutually inverse rectangular coefficient matrices induce an isomorphism
on the actual polynomial vector groups. -/
def rectangularMatrixIso (M : Matrix (Fin m) (Fin n) R)
    (N : Matrix (Fin n) (Fin m) R) (hNM : N * M = 1) (hMN : M * N = 1) :
    groupScheme R n ≅ groupScheme R m where
  hom := matrixHom M
  inv := matrixHom N
  hom_inv_id := by rw [matrixHom_comp, hNM, matrixHom_one]
  inv_hom_id := by rw [matrixHom_comp, hMN, matrixHom_one]

/-- A linear equivalence of finite coordinate modules gives an isomorphism
on all scheme tests, including nonreduced tests. -/
def linearIso (e : (Fin n → R) ≃ₗ[R] (Fin m → R)) :
    groupScheme R n ≅ groupScheme R m :=
  rectangularMatrixIso (LinearMap.toMatrix' e.toLinearMap)
    (LinearMap.toMatrix' e.symm.toLinearMap)
    (by rw [← LinearMap.toMatrix'_comp]; simp)
    (by rw [← LinearMap.toMatrix'_comp]; simp)

@[simp]
theorem coordinates_linearIso (e : (Fin n → R) ≃ₗ[R] (Fin m → R))
    (T : Over (Spec R)) (x : T ⟶ (groupScheme R n).X) :
    (coordinates R m T (x ≫ (linearIso e).hom.hom.hom)).toAdd =
      (LinearMap.toMatrix' e.toLinearMap).map (scalarMap T) *ᵥ
        (coordinates R n T x).toAdd :=
  coordinates_matrixHom _ _ _

/-- Coefficient-ring sections of a matrix homomorphism have the original
coefficient matrix, with no spectrum-coordinate change left over. -/
theorem sectionCoordinates_matrixHom_map (M : Matrix (Fin m) (Fin n) R)
    (x : rationalPoints (groupScheme R n)) :
    (sectionCoordinates R m (rationalPoints.map (matrixHom M) x)).toAdd =
      M *ᵥ (sectionCoordinates R n x).toAdd := by
  have hc (c : R) : (Scheme.ΓSpecIso R).hom.hom
      (scalarMap (Over.mk (𝟙 (Spec R))) c) = c := by
    change ((Scheme.ΓSpecIso R).inv ≫ (𝟙 (Spec R) : Spec R ⟶ Spec R).appTop ≫
      (Scheme.ΓSpecIso R).hom) c = c
    simp
  change (fun j => (Scheme.ΓSpecIso R).hom.hom
    ((coordinates R m (Over.mk (𝟙 _))
      (x ≫ (matrixHom M).hom.hom)).toAdd j)) = _
  rw [coordinates_matrixHom]
  funext j
  rw [RingHom.map_mulVec]
  have hM : (M.map (scalarMap (Over.mk (𝟙 (Spec R))))).map
      (Scheme.ΓSpecIso R).hom.hom = M := by
    ext i l
    exact hc (M i l)
  rw [hM]
  rfl

@[simp]
theorem sectionCoordinates_linearIso (e : (Fin n → R) ≃ₗ[R] (Fin m → R))
    (x : rationalPoints (groupScheme R n)) :
    (sectionCoordinates R m (rationalPoints.map (linearIso e).hom x)).toAdd =
      e (sectionCoordinates R n x).toAdd := by
  rw [linearIso, rectangularMatrixIso, sectionCoordinates_matrixHom_map,
    LinearMap.toMatrix'_mulVec]
  rfl

end Langlands.GroupScheme.VectorGroup
