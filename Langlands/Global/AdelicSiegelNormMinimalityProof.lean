import Langlands.Global.AdelicSiegelNormMinimalityAssembly
import Langlands.Global.AdelicSiegelDiagonalHeightBound

/-!
# Proof of polynomial norm minimality on actual adelic Siegel products

This module proves `SiegelNormMinimalityStatement` by combining the diagonal height
inequality `exists_adelicHeight_map_le_rational_mul` with the assembly theorem
`siegelNormMinimalityStatement_of_diagonal`. The paired Markdown records the argument.
-/

noncomputable section

universe u

namespace Langlands.Global.AdelicSiegelFactors

/-- **Mœglin–Waldspurger I.2.2 (vii), polynomial form.** On every actual weak Siegel product
of an actual algebraic Siegel setup, the full adelic height of a point is bounded by a constant
times the height of each of its rational left translates. -/
theorem siegelNormMinimalityStatement : SiegelNormMinimalityStatement.{u} :=
  siegelNormMinimalityStatement_of_diagonal fun F _ _ G _ _ _ rho hN T₀ hT₀ f =>
    exists_adelicHeight_map_le_rational_mul F G rho hN T₀ hT₀ f

end Langlands.Global.AdelicSiegelFactors
