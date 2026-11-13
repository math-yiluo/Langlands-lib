import Langlands.Geometry.Building.IntegerValuationAffineWeylStatement
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.Geometry.Building.IntegerAffineRootFibreInfinitude

/-! # Integer-valuation affine root systems and affine Weyl containment -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- The ordinary affine roots satisfy corrected AR 1--AR 4, allowing rank zero. -/
theorem isAffineRootSystemWithRankZero_affineRoots
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) :
    AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots := by
  have hΨ :=
    B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs B.hasOppositeFactorPairs
  exact
    { span_derivativeRoots_eq_top := hΨ.span_derivativeRoots_eq_top
      linear_ne_zero := hΨ.linear_ne_zero
      finite_derivativeRoots := hΨ.finite_derivativeRoots
      exists_isCoroot := hΨ.exists_isCoroot
      coroot_integral := fun _ hψ _ hθ _ hw => B.coroot_integral_affineRoots hψ hθ hw
      infinite_fiber := fun _ hψ => B.infinite_fiber_affineRoots hunit hψ
      finite_bounded := fun ψ _ M => by
        let x : B.Apartment := Classical.arbitrary B.Apartment
        refine (hΨ.finite_bounded_at x fun _ => M + |ψ x|).subset ?_
        rintro θ ⟨hθ, -, hM⟩
        refine ⟨hθ, ?_⟩
        calc |θ x| = |(θ x - ψ x) + ψ x| := by ring_nf
          _ ≤ |θ x - ψ x| + |ψ x| := abs_add_le _ _
          _ ≤ M + |ψ x| := add_le_add (hM x) le_rfl }

end IntegerValuationBuildingData

/-- The exact field-independent affine-root-system and affine-Weyl target. -/
theorem integerValuationAffineWeyl :
    IntegerValuationAffineWeylStatement.{u} := by
  intro k _ v hunit G _ B
  exact ⟨B.isAffineRootSystemWithRankZero_affineRoots hunit, B.affineWeylGroup_le_range⟩

end Langlands.Geometry.Building
