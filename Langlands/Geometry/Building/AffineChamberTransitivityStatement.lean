import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-! # Simple transitivity of the affine Weyl group on chambers -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building

/-- The chamber consequence of KP Lemma 1.3.17: between any two chambers there is
exactly one element of the existing reflection-generated affine Weyl group.
The derivative-spanning root-system predicate includes rank zero. -/
def AffineChamberSimpleTransitivityStatement : Prop :=
  ∀ (V : Type uV) (A : Type uA) [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (Ψ : Set (A →ᵃ[ℝ] ℝ)),
    AffineRootSystem.IsAffineRootSystemWithRankZero Ψ →
      ∀ C D : Set A, AffineRootSystem.IsChamber Ψ C →
        AffineRootSystem.IsChamber Ψ D →
          ∃! w : AffineRootSystem.affineWeylGroup Ψ,
            (w : A ≃ᵃ[ℝ] A) '' C = D

end Langlands.Geometry.Building
