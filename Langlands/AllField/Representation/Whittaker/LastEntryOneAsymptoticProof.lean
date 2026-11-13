import Langlands.Representation.Whittaker.LastEntryOneAsymptoticProof
import Langlands.AllField.Representation.Whittaker.JPSDecompositionProof
import Langlands.AllField.Representation.Whittaker.LastEntryOneGerms
/-!
# Last-entry-one expansion for finite-type Whittaker representations

The actual root coefficient image satisfies the three hypotheses of the
published JPS function-space decomposition. Pullback along consecutive
quotients and scalar uniqueness give the exact closed target.
-/

noncomputable section

namespace Langlands.AllField

open Langlands.WhittakerLastEntryOne hiding assemble continuous_rootLiftHom coordinateBlockScalars coordinateJacquetRepresentation coordinateJacquetRepresentation_mk coordinateJacquetToRootGerm coordinateJacquetToRootGerm_surjective jacquetToRootGerm jacquetToRootGerm_mk jacquetToRootGerm_surjective pullback_injective rootCoefficientMap rootCoefficientMap_apply rootCoefficientSpace rootCoefficientSpace_finiteCoordinateOperatorSpan rootCoefficientSpace_finiteOperatorSpans rootCoefficientSpace_hasCoordinateUpperSupport rootCoefficientSpace_hasCoordinateUpperSupport_of_statement rootCoefficientSpace_isLocallyConstantSpace rootCoefficientSpace_locallyConstant rootCoefficientSpace_upper_support rootCoefficientToSpace rootCoefficientToSpace_surjective rootCoefficient_kernel rootGermMap rootGermMap_coordinate rootGermMap_eq_zero_iff rootGermMap_surjective rootHom_rootLift rootLiftHom rootLift_coordinateEmbedding rootLift_last rootLift_rootHom torus_rootLift_coordinateEmbedding upper_support_of_statement
open Langlands.AllField.WhittakerLastEntryOne

open scoped BigOperators

universe uF uV

/-- JPS (1979), Proposition (2.2) and Remark (2.2.5), on diagonals whose
last entry is one, with a finite family uniform in the functional and vector. -/
theorem whittakerLastEntryOneAsymptotic :
    WhittakerLastEntryOneAsymptoticStatement.{uF,uV} := by
  intro F _ T
  let := T.topology
  intro n V _ _ ρ ψ hc hne hu hρ hfinite
  dsimp only
  intro hWhittaker
  obtain ⟨ℓ₀, _, hℓ₀, hspan⟩ := hWhittaker
  obtain ⟨X, hX, hexpansion⟩ :=
    Langlands.AllField.Whittaker.jpsDecomposition F T n
      (rootCoefficientSpace F T n V ρ ℓ₀)
      (rootCoefficientSpace_isLocallyConstantSpace F T
        n V ρ ℓ₀ hρ.1)
      (rootCoefficientSpace_hasCoordinateUpperSupport F T
        n V ρ ℓ₀ ψ hc hne hu hρ.1 hℓ₀)
      (rootCoefficientSpace_finiteOperatorSpans F
        T n V ρ ℓ₀
        ψ hc hu hρ hfinite hℓ₀)
  apply assemble F T n V ρ _ ℓ₀ hspan X
  · exact hX
  · intro v
    exact hexpansion
      (rootCoefficientToSpace F T n V ρ ℓ₀ v)

end Langlands.AllField
