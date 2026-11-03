import Langlands.GroupScheme.Chevalley.ActualLineStabilizer
import Langlands.GroupScheme.Chevalley.UnipotentLine
import Langlands.GroupScheme.VectorOrbit
import Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement

/-! # Affine vector orbit maps with prescribed unipotent stabilizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.Chevalley

/-- A closed unipotent subgroup of an affine finite-type group is the exact
all-test vector stabilizer in an actual finite matrix representation. -/
theorem exists_vector_stabilizer
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hc : IsClosedSubgroup i) (hH : IsUnipotent H) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
        x ∈ (SubgroupFunctor.range i).carrier T ↔
          (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
            Pi.single j 1 = Pi.single j 1 := by
  obtain ⟨n, j, ρ, hρ⟩ := exists_line_stabilizer k G H i hc
  exact ⟨n, j, ρ, MatrixRepresentation.range_iff_fixes_coordinateLine_of_isUnipotent
    i ρ j hH hρ⟩

/-- The actual affine vector orbit map realizes all coset fibers of the closed
unipotent subgroup, over every relative scheme test. -/
theorem exists_affine_vector_orbit
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hc : IsClosedSubgroup i) (hH : IsUnipotent H) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ VectorOrbit.orbitMap ρ j = h ≫ VectorOrbit.orbitMap ρ j ↔
          g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  obtain ⟨n, j, ρ, hρ⟩ := exists_vector_stabilizer k G H i hc hH
  refine ⟨n, j, ρ, fun T g h => ?_⟩
  exact (VectorOrbit.orbitMap_fibers ρ j T g h).trans (hρ T (g⁻¹ * h)).symm

variable {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual affine coordinate-vector orbit map with exact prescribed coset fibers. -/
structure AffineVectorOrbit (i : H ⟶ G) where
  dimension : ℕ
  coordinate : Fin (dimension + 1)
  representation : MatrixRepresentation G (Fin (dimension + 1))
  fibers : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
    g ≫ VectorOrbit.orbitMap representation coordinate =
        h ≫ VectorOrbit.orbitMap representation coordinate ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T

/-- Choose an affine vector orbit map for a closed unipotent subgroup. -/
def affineVectorOrbit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : H ⟶ G) (hc : IsClosedSubgroup i) (hH : IsUnipotent H) :
    AffineVectorOrbit i := by
  exact Classical.choice (by
    obtain ⟨n, j, ρ, hρ⟩ := exists_affine_vector_orbit k G H i hc hH
    exact ⟨⟨n, j, ρ, hρ⟩⟩)

/-- The published Kostant–Rosenlicht statement, when supplied, makes these
actual affine vector orbits closed for a smooth unipotent ambient group. -/
theorem exists_closed_affine_vector_orbit
    (hclosed : UnipotentAffineOrbitClosedStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] (hG : IsUnipotent G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G)
    (hc : IsClosedSubgroup i) (hH : IsUnipotent H) :
    ∃ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
      IsClosed (Set.range (VectorOrbit.orbitMap ρ j).left) ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
        g ≫ VectorOrbit.orbitMap ρ j = h ≫ VectorOrbit.orbitMap ρ j ↔
          g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  obtain ⟨n, j, ρ, hfib⟩ := exists_affine_vector_orbit k G H i hc hH
  have : IsAffine (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin (n + 1)) (CommRingCat.of k))))
    infer_instance
  have : LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of k) (n + 1)).X.hom := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr
      (inferInstance : Algebra.FiniteType (CommRingCat.of k)
        (MvPolynomial (Fin (n + 1)) (CommRingCat.of k)))
  exact ⟨n, j, ρ, hclosed k G hG _ (VectorOrbit.schemeAction ρ)
    (VectorOrbit.coordinatePoint _ _ j _), hfib⟩

end Langlands.GroupScheme.Chevalley
