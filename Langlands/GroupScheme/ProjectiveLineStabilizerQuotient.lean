import Langlands.GroupScheme.ProjectiveOrbit
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.CoordinateLines
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Homogeneous quotients from coordinate-line stabilizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.ProjectiveOrbit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (n : ℕ)

/-- Pullback of the canonical coordinate section is the same coordinate section. -/
@[simp]
theorem pullbackPoint_basisSection {S T : Scheme.{u}} (f : T ⟶ S)
    (j : Fin (n + 1)) :
    pullbackPoint n (RelativeProjectiveSpace.basisSection n S j) f =
      RelativeProjectiveSpace.basisSection n T j := by
  apply RelativeProjectiveSpace.hom_ext
  · simp
  · rw [pullbackPoint_toIntegral, ← Category.assoc,
      RelativeProjectiveSpace.basisSection_naturality, Category.assoc,
      RelativeProjectiveSpace.map_toIntegral]

/-- A matrix fixes the actual coordinate section exactly when it scales the
coordinate vector by one global unit. -/
theorem basisSection_matrixAction_eq_iff (T : Scheme.{u}) (j : Fin (n + 1))
    (M : GL (Fin (n + 1)) Γ(T, ⊤)) :
    RelativeProjectiveSpace.basisSection n T j ≫ matrixAction n M =
        RelativeProjectiveSpace.basisSection n T j ↔
      ∃ a : Γ(T, ⊤)ˣ,
        (M : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T, ⊤)) *ᵥ Pi.single j 1 =
          (a : Γ(T, ⊤)) • (Pi.single j (1 : Γ(T, ⊤)) :
            Fin (n + 1) → Γ(T, ⊤)) := by
  simpa only [matrixAction, coordinateEquiv_apply, Units.smul_def] using
    RelativeProjectiveSpace.basisSection_globalLinearAction_eq_iff n T j
      (coordinateEquiv n M)

/-- The projective orbit of a coordinate line has exactly the right-coset
fibers of its prescribed all-test line stabilizer. -/
theorem basisSection_orbitMap_fibers
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    (i : H ⟶ G) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1)))
    (hρ : ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range i).carrier T ↔
        ∃ a : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
              Pi.single j 1 =
            (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) :
              Fin (n + 1) → Γ(T.left, ⊤)))
    (T : Over (Spec R)) (g h : T ⟶ G.X) :
    g ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n (Spec R) j) =
        h ≫ orbitMap n ρ (RelativeProjectiveSpace.basisSection n (Spec R) j) ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  rw [orbitMap_fibers, pullbackPoint_basisSection, basisSection_matrixAction_eq_iff]
  exact (hρ T (g⁻¹ * h)).symm

/-- Choose the full actual homogeneous quotient from an all-test coordinate-line
stabilizer representation. -/
def quotientOfLineStabilizer
    {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (hH : Smooth H.X.hom)
    (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1)))
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range i).carrier T ↔
        ∃ a : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(T.left, ⊤)) *ᵥ
              Pi.single j 1 =
            (a : Γ(T.left, ⊤)) • (Pi.single j (1 : Γ(T.left, ⊤)) :
              Fin (n + 1) → Γ(T.left, ⊤))) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient i :=
  HomogeneousQuotientFromEmbedding.quotientOfMapKernel i hi hH
    (ambient n (CommRingCat.of k))
    (orbitMap n ρ (RelativeProjectiveSpace.basisSection n (Spec (CommRingCat.of k)) j))
    (basisSection_orbitMap_fibers n i j ρ hρ)

end Langlands.GroupScheme.ProjectiveOrbit
