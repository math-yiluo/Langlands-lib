import Langlands.Representation.Whittaker.LastEntryOneGerms
import Langlands.Representation.Whittaker.JPSDecompositionProof

/-!
# Last-entry-one expansion for finite-type Whittaker representations

The actual root coefficient image satisfies the three hypotheses of the
published JPS function-space decomposition. Pullback along consecutive
quotients and scalar uniqueness give the exact closed target.
-/

noncomputable section

namespace Langlands

open WhittakerLastEntryOne

open scoped BigOperators

universe uF uV

/-- JPS (1979), Proposition (2.2) and Remark (2.2.5), on diagonals whose
last entry is one, with a finite family uniform in the functional and vector. -/
theorem whittakerLastEntryOneAsymptotic :
    WhittakerLastEntryOneAsymptoticStatement.{uF,uV} := by
  intro p hp F
  let := F.canonicalTopologicalData.topology
  intro n V _ _ ρ ψ hc hne hu hρ hfinite
  dsimp only
  intro hWhittaker
  obtain ⟨ℓ₀, _, hℓ₀, hspan⟩ := hWhittaker
  obtain ⟨X, hX, hexpansion⟩ :=
    Whittaker.jpsDecomposition p F F.canonicalTopologicalData n
      (rootCoefficientSpace F F.canonicalTopologicalData n V ρ ℓ₀)
      (rootCoefficientSpace_isLocallyConstantSpace F F.canonicalTopologicalData
        n V ρ ℓ₀ hρ.1)
      (rootCoefficientSpace_hasCoordinateUpperSupport F F.canonicalTopologicalData
        n V ρ ℓ₀ ψ hc hne hu hρ.1 hℓ₀)
      (rootCoefficientSpace_finiteOperatorSpans F
        F.canonicalTopologicalData n V ρ ℓ₀
        ψ hc hu hρ hfinite hℓ₀)
  apply assemble F F.canonicalTopologicalData n V ρ _ ℓ₀ hspan X
  · exact hX
  · intro v
    exact hexpansion
      (rootCoefficientToSpace F F.canonicalTopologicalData n V ρ ℓ₀ v)

end Langlands
