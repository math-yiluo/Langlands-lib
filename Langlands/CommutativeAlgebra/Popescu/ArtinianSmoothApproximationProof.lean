import Langlands.CommutativeAlgebra.Popescu.SmoothApproxFinal
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityH1FiniteProof
import Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatProof
import Langlands.CommutativeAlgebra.Popescu.ArtinianEtaleCriterionProof
import Langlands.CommutativeAlgebra.Popescu.ArtinianUnitEnlargementProof
import Langlands.CommutativeAlgebra.Popescu.ArtinianFlatSubalgebra
import Langlands.CommutativeAlgebra.Popescu.RegularParameterExtensionProof

/-!
# Stacks 07FH: essentially smooth approximation of truncated local rings

`SmoothApprox.artinianSmoothApproximation_of` applied to the published proofs of its six input
statements.
-/

namespace Langlands.CommutativeAlgebra.Popescu

universe u

/-- **Stacks 07FH** (Smoothing Ring Maps, Lemma 16.11.2). Let `k` be a field of characteristic
`p > 0`, `Λ` a Noetherian geometrically regular `k`-algebra, `q ⊂ Λ` a prime, `n ≥ 1` and
`E ⊂ Λ_q/qⁿΛ_q` finite. Then there are `m`, `φ : k[y₁, …, y_m] → Λ` with `𝔭 = φ⁻¹(q)`,
`𝔭Λ_q = qΛ_q` and `k[y]_𝔭 → Λ_q` flat, and a factorization
`k[y]_𝔭/𝔭ⁿk[y]_𝔭 → D → Λ_q/qⁿΛ_q` through a local Artinian ring `D`, essentially smooth over
`k[y]_𝔭/𝔭ⁿk[y]_𝔭`, with `ψ : D → Λ_q/qⁿΛ_q` flat and local and `E ⊆ ψ(D)`. -/
theorem artinianSmoothApproximation : ArtinianSmoothApproximationStatement.{u} :=
  SmoothApprox.artinianSmoothApproximation_of geometricRegularityH1Finite
    GeometricRegularity.geometricRegularityFlat regularParameterExtension
    artinianFlatSubalgebra Enlargement.artinianUnitEnlargement
    EtaleCriterion.artinianEtaleCriterion

end Langlands.CommutativeAlgebra.Popescu
