import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1FiniteStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveStatement
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1InjectiveProof
import Mathlib

/-! # Finiteness of `H₁(L_{κ(q)/k})` from the injectivity into `𝔪/𝔪²` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- `H₁(L_{κ(q)/k})` embeds into the finite-dimensional `H₁(L_{κ(q)/Λ_q}) = 𝔪/𝔪²`. -/
theorem geometricRegularityH1Finite_of (h : GeometricRegularityH1InjectiveStatement.{u}) :
    GeometricRegularityH1FiniteStatement.{u} := by
  intro k Λ _ _ _ p _ _ hreg q _
  have : IsNoetherianRing Λ := hreg.1
  have hinj := h k Λ p hreg q
  have : Algebra.FinitePresentation (Localization.AtPrime q) q.ResidueField :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Finite q.ResidueField
      (Algebra.H1Cotangent (Localization.AtPrime q) q.ResidueField) := inferInstance
  exact Module.Finite.of_injective _ hinj

/-- **Finiteness of `H₁(L_{κ(q)/k})`.** For a geometrically regular algebra `Λ` over a field `k`
of characteristic `p > 0` and a prime `q` of `Λ`, `H₁(L_{κ(q)/k})` is a finite-dimensional
`κ(q)`-vector space. -/
theorem geometricRegularityH1Finite : GeometricRegularityH1FiniteStatement.{u} :=
  geometricRegularityH1Finite_of GeometricRegularityH1.geometricRegularityH1Injective

end Langlands.CommutativeAlgebra.Popescu
