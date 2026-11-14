import Langlands.GroupScheme.IntegralModel.MaximalBounded
import Langlands.GroupScheme.BoundedSubgroupStableLatticeProof
import Langlands.GroupScheme.IntegralModel.GeneralLinearLatticeProof
import Langlands.GroupScheme.IntegralModel.SchematicClosureProof
import Langlands.GroupScheme.IntegralModel.SmootheningProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Smooth integral models of maximal algebraically bounded subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

/-- The maximal-subgroup construction in KP Proposition 8.3.1, using the published
stable-lattice, general-linear-model, schematic-closure and smoothening theorems. -/
theorem maximalBoundedIntegralModel : MaximalBoundedIntegralModelStatement.{u} := by
  intro K _ _ _ _ _ G _ hG B hB
  let : Smooth G.X.hom := hG
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement K G inferInstance inferInstance
  obtain ⟨Λ, hΛ⟩ := boundedSubgroupStableLattice K G n ρ B hB.1
  obtain ⟨M, _, hM⟩ := generalLinearLatticeIntegralModel (valuation K).integer K n Λ hΛ.1
  let D : Subgroup (rationalPoints G) :=
    M.integralPoints.comap (rationalPoints.map ρ)
  have hmat (g : rationalPoints G) :
      GeneralLinear.rationalPointsEquiv n (CommRingCat.of K) (rationalPoints.map ρ g) =
        ρ.rationalMatrix g := by
    apply Units.ext
    rfl
  have hBD : B ≤ D := by
    intro g hg
    apply (hM _).mpr
    change
      (∀ v ∈ Λ,
        (GeneralLinear.rationalPointsEquiv n (CommRingCat.of K)
          (rationalPoints.map ρ g) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Λ) ∧
      (∀ v ∈ Λ,
        ((GeneralLinear.rationalPointsEquiv n (CommRingCat.of K)
          (rationalPoints.map ρ g))⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Λ)
    rw [hmat]
    refine ⟨hΛ.2 g hg, ?_⟩
    simpa only [map_inv, Matrix.coe_units_inv] using hΛ.2 (g⁻¹) (B.inv_mem hg)
  have hD : IsAlgebraicallyBounded K G.X (D : Set (rationalPoints G)) := by
    apply ρ.isAlgebraicallyBounded_of_preserves_lattice hρ D Λ hΛ.1
    intro g hg
    have h := (hM (rationalPoints.map ρ g)).mp hg
    simpa only [hmat] using h.1
  have hEq : B = D := hB.eq_of_le hD hBD
  obtain ⟨C, φ, hφ⟩ := integralModelSchematicClosure (valuation K).integer K
    (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)) M G ρ hρ
  have hC : C.integralPoints = D := hφ.integralPoints_eq_comap
  obtain ⟨L, π, hπ⟩ := IntegralModel.smoothening_exists (valuation K).integer K G hG C
  exact ⟨L, hπ.1, hπ.integralPoints_eq.trans (hC.trans hEq.symm)⟩

end Langlands.GroupScheme
