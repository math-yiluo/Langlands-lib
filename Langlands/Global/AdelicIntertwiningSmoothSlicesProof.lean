import Langlands.Global.AdelicIntertwiningSmoothSlicesReduction
import Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthProof

/-! # Smooth infinite slices of regular intertwining integrals

A proof of `IntertwiningSmoothSlicesStatement` (Mœglin–Waldspurger II.1.6 (i)): the implication
`intertwiningSmoothSlicesReduction` applied to the uniformly moderate growth of automorphic
functions, `automorphicFunctionUniformGrowth`. -/

universe u

namespace Langlands.Global

/-- **Mœglin–Waldspurger 1995, II.1.6 (i), smoothness.** For the data of
`IntertwiningSmoothSlicesStatement` there is a real `R₀` such that for every `R₀`-regular `λ` every
infinite slice of the intertwining operator `M(w, λ)φ` is plot-smooth. -/
theorem intertwiningSmoothSlices : IntertwiningSmoothSlicesStatement.{u} :=
  intertwiningSmoothSlicesReduction.{u}
    Langlands.Automorphic.GroupSchemeFunctions.automorphicFunctionUniformGrowth.{u}

end Langlands.Global
