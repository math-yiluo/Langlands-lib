import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.Dynamic.GeneralLinearBaseChange
import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.Algebra.Module.Lattice
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # General linear integral models attached to actual full lattices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace GeneralLinear

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The standard general linear group over the integral base, with the Library's
base-change identification over the supplied fraction field. Flatness and local
finite type come from the published smoothness of the general linear group. -/
def standardIntegralModel (n : Type) [Fintype n] [DecidableEq n] :
    IntegralModel R K (groupScheme n (CommRingCat.of K)) where
  group := groupScheme n (CommRingCat.of R)
  affine := isAffineHom_groupScheme (n := n) (R := CommRingCat.of R)
  flat :=
    haveI : Smooth (groupScheme n (CommRingCat.of R)).X.hom :=
      smoothStatement n (CommRingCat.of R)
    inferInstance
  finiteType :=
    haveI : Smooth (groupScheme n (CommRingCat.of R)).X.hom :=
      smoothStatement n (CommRingCat.of R)
    inferInstance
  genericIso := baseChangeIso n (Spec.algebraMap R K)

/-- Smoothness of the standard model follows from the published smoothness
of the actual general linear group scheme. -/
theorem standardIntegralModel_isSmooth (n : Type) [Fintype n] [DecidableEq n] :
    (standardIntegralModel R K n).IsSmooth :=
  smoothStatement n (CommRingCat.of R)

variable {R K} {n : ℕ}

/-- A rational point stabilizes the original lattice exactly when both its actual
matrix and its inverse matrix carry that lattice into itself. -/
def StabilizesLattice (Λ : Submodule R (Fin n → K))
    (g : rationalPoints (groupScheme (Fin n) (CommRingCat.of K))) : Prop :=
  (∀ v ∈ Λ, (rationalPointsEquiv n (CommRingCat.of K) g :
    Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Λ) ∧
  (∀ v ∈ Λ, ((rationalPointsEquiv n (CommRingCat.of K) g)⁻¹ :
    Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Λ)

end GeneralLinear

/-- Every full lattice in the coordinate vector space over the fraction field of a
discrete valuation ring has a smooth integral model of the fixed generic general
linear group whose integral points are exactly the lattice stabilizer. -/
def GeneralLinearLatticeIntegralModelStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (n : ℕ) (Λ : Submodule R (Fin n → K)),
    Submodule.IsLattice K Λ →
      ∃ M : IntegralModel R K (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)),
        M.IsSmooth ∧
          ∀ g, g ∈ M.integralPoints ↔ GeneralLinear.StabilizesLattice Λ g

end Langlands.GroupScheme
