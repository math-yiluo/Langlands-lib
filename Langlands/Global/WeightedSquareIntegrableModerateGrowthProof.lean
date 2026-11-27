import Langlands.Global.AdelicWeightedModerateGrowthReduction
import Langlands.Global.AdelicReproducingKernelProof
import Langlands.Global.AdelicRationalConjugateCountingAllPointsProof

/-! # Moderate growth of weighted square-integrable automorphic functions -/

set_option autoImplicit false

namespace Langlands.Global

/-- Weighted square-integrable, smooth, `K_∞`-finite and `𝔷`-finite left `G(F)`-invariant
functions on `G(𝔸)` have moderate growth (Harish-Chandra 1966, §8, Theorem 1, and
Mœglin–Waldspurger I.2.4 (a)(i), as in the proof of Mœglin–Waldspurger I.2.5 (b)). -/
theorem weightedSquareIntegrableModerateGrowth :
    WeightedSquareIntegrableModerateGrowthStatement :=
  weightedSquareIntegrableModerateGrowth_of_reduction adelicReproducingKernel
    adelicRationalConjugateCountingAllPoints.{0}

end Langlands.Global
