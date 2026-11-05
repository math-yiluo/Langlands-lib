import Langlands.Representation.Plancherel.RationalModerateGrowthStatement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Polynomial coefficient bounds on compact actual lattice charts -/

noncomputable section

universe u uV uI

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

open GroupScheme MatrixRepresentation

/-- A coordinate lower bound for the actual matrix norm converts unrestricted
product-exponential coefficient bounds into polynomial bounds, uniformly over
compact outer translates and a finite middle translate. -/
def RationalCompactLatticePolynomialBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n]
      (ρ : MatrixRepresentation G n)
      (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
      (I : Type uI) [Fintype I] (τ : (I → ℕ) → rationalPoints G),
      (∀ (φ : SmoothDual π.representation) (v : π),
        ∃ a : I → ℝ, (∀ i, 0 < a i) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ m : I → ℕ,
            ‖(φ : Module.Dual ℂ π) (π.representation (τ m) v)‖ ≤
              C * ∏ i, a i ^ m i) →
      (∃ q A : ℝ, 1 < q ∧ 0 < A ∧ ∀ m : I → ℕ,
        q ^ (∑ i, m i) ≤ A * rationalMatrixNorm F ρ (τ m)) →
      ∀ (S₁ S₂ T : Set (rationalPoints G)), IsCompact S₁ → IsCompact S₂ → T.Finite →
        ∀ (φ : SmoothDual π.representation) (v : π),
          ∃ (d : ℕ) (c : ℝ), 0 < c ∧
            ∀ (m : I → ℕ) (k₁ : rationalPoints G), k₁ ∈ S₁ →
              ∀ t : rationalPoints G, t ∈ T →
                ∀ k₂ : rationalPoints G, k₂ ∈ S₂ →
                  ‖(φ : Module.Dual ℂ π)
                    (π.representation (k₁ * τ m * t * k₂) v)‖ ≤
                      c * rationalMatrixNorm F ρ (k₁ * τ m * t * k₂) ^ d

end Langlands.Plancherel
