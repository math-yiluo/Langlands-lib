import Langlands.GroupScheme.CentralSimpleNormOneSplitting

/-! # Split reduced-norm-one groups over the original ground field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits.Splitting

open Langlands.CentralSimple Langlands.ReducedNorm

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  (e : K ⊗[K] A ≃ₐ[K]
    Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) K)

/-- Points of a norm-one group split over the ground field are determinant-one section matrices. -/
def groundPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (normOne K A).X) ≃*
      Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ(T.left, ⊤) :=
  (normOnePointsEquiv K A T).trans
    (coefficientEquiv K A e ((algΓ (CommRingCat.of K)).obj T).unop)

/-- The point comparison uses the given chart on the actual coefficient tensor unit. -/
theorem groundPointsEquiv_val (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (normOne K A).X) :
    (groundPointsEquiv K A e T x : Matrix _ _ Γ(T.left, ⊤)) =
      splittingMap e ((algΓ (CommRingCat.of K)).obj T).unop
        ((normOnePointsEquiv K A T x).val :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] A) := rfl

/-- The ground-field point comparison respects every relative test restriction. -/
theorem groundPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (normOne K A).X) :
    groundPointsEquiv K A e T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map a.left.appTop.hom (groundPointsEquiv K A e T x) := by
  apply Subtype.ext
  rw [groundPointsEquiv_val, normOnePointsEquiv_naturality]
  change splittingMap e ((algΓ (CommRingCat.of K)).obj T').unop
    (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
      (AlgHom.id K A) _) = _
  rw [splittingMap_naturality K A e _
    (fun r => ((algΓ (CommRingCat.of K)).map a).unop.hom.commutes r)]
  rfl

/-- The actual split norm-one group is special linear over its original base. -/
def groundIso : normOne K A ≅
    SpecialLinear.groupScheme (Fin (reducedDegree K A)) (CommRingCat.of K) :=
  isoOfPointModels (fun T =>
      Matrix.SpecialLinearGroup (Fin (reducedDegree K A)) Γ(T.left, ⊤))
    (fun a => Matrix.SpecialLinearGroup.map a.left.appTop.hom)
    (groundPointsEquiv K A e)
    (SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of K))
    (groundPointsEquiv_naturality K A e)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y)

/-- The scheme isomorphism retains the specified all-test chart. -/
theorem groundIso_hom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (normOne K A).X) :
    SpecialLinear.pointsEquiv (Fin (reducedDegree K A)) (CommRingCat.of K) T
      (x ≫ (groundIso K A e).hom.hom.hom) = groundPointsEquiv K A e T x :=
  isoOfPointModels_hom _ _ _ _ (groundPointsEquiv_naturality K A e)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y) T x

end Langlands.GroupScheme.CentralSimpleUnits.Splitting

namespace Langlands.GroupScheme.CentralSimpleUnits

open Langlands.CentralSimple

variable (K : Type u) [Field K]

/-- The actual binary matrix algebra has dimension four. -/
theorem binaryMatrix_finrank : Module.finrank K (Matrix (Fin 2) (Fin 2) K) = 4 := by
  simp [Module.finrank_matrix]

/-- The reduced degree of the binary matrix algebra is two. -/
theorem binaryMatrix_reducedDegree : reducedDegree K (Matrix (Fin 2) (Fin 2) K) = 2 := by
  rw [reducedDegree, binaryMatrix_finrank]
  exact Nat.sqrt_eq 2

/-- The split chart is the canonical left-unit tensor equivalence. -/
def binaryMatrixChart : K ⊗[K] Matrix (Fin 2) (Fin 2) K ≃ₐ[K]
    Matrix (Fin (reducedDegree K (Matrix (Fin 2) (Fin 2) K)))
      (Fin (reducedDegree K (Matrix (Fin 2) (Fin 2) K))) K := by
  rw [binaryMatrix_reducedDegree K]
  exact Algebra.TensorProduct.lid K (Matrix (Fin 2) (Fin 2) K)

/-- The actual norm-one binary matrix group is the published split special-linear group. -/
def binaryMatrixNormOneIso : normOne K (Matrix (Fin 2) (Fin 2) K) ≅
    SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K) := by
  have h := Splitting.groundIso K (Matrix (Fin 2) (Fin 2) K) (binaryMatrixChart K)
  rw [binaryMatrix_reducedDegree K] at h
  exact h

end Langlands.GroupScheme.CentralSimpleUnits
