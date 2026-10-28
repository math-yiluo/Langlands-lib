import Langlands.Representation.Classification.FineOppositeJacquetHomFinitenessStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
import Langlands.Representation.Smooth.IntertwinerFiniteness

/-! Finite-dimensional actual fine opposite-Jacquet intertwiner spaces. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uZ

/-- The exact closed finiteness statement for both actual opposite Jacquet targets. -/
theorem fineOppositeJacquetHomFinite :
    FineOppositeJacquetHomFinitenessStatement.{uF, uV, uW, uZ} := by
  intro p _ F T
  let := T.topology
  intro n B S ω hωirr hωcusp v₀ t
  let τ := fineTwist T B S ω v₀ t
  have hτ := fineTwistIrreducibleAdmissible p F T n B S ω hωirr hωcusp v₀ t
  let : Representation.IsIrreducible τ.ρ := hτ.1
  have hfinite : Module.Finite
      (MonoidAlgebra ℂ (refinedLevi F.Carrier B S)) τ.ρ.asModule := inferInstance
  constructor
  · intro π hπ
    exact finite_intertwiningMap_of_finiteType τ.ρ _ hτ.2.1.1 hfinite
      (Parabolic.isAdmissible_normalizedRefinedOppositeJacquet F T B S _ π.ρ hπ)
  · intro J hJ
    exact finite_intertwiningMap_of_finiteType τ.ρ _ hτ.2.1.1 hfinite
      (Parabolic.isAdmissible_normalizedComposedOppositeJacquet F T B S _ J.ρ hJ)

end Langlands
