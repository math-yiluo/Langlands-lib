import Langlands.Representation.Archimedean.ComplexJacquetModuleFiniteReduction
import Langlands.Representation.Archimedean.LowerVermaKostant
import Langlands.Representation.Archimedean.LowerVermaHomBound
import Langlands.Representation.Archimedean.LowerVermaProjective

/-!
# Casselman's theorem for `(𝔤𝔩_n(ℂ), U(n))`-modules

`complexJacquetModuleFinite` proves `ComplexJacquetModuleFiniteStatement`: the Jacquet module
`V/𝔫V` of an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module is finite-dimensional and nonzero.
It applies the reduction `complexJacquetModuleFiniteReduction` to the proofs of the six
Bernstein–Gelfand inputs on lower Verma modules. See the paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- Casselman's theorem for `(𝔤𝔩_n(ℂ), U(n))`-modules: for an irreducible admissible module the
Jacquet module `V/𝔫V` is finite-dimensional and nonzero. -/
theorem complexJacquetModuleFinite : ComplexJacquetModuleFiniteStatement.{uV} :=
  complexJacquetModuleFiniteReduction ⟨VermaPBW.lowerVermaWeight, VermaPBW.lowerVermaDuflo,
    VermaKostant.lowerVermaKostant, VermaCentral.lowerVermaCentral, VermaPBW.lowerVermaHomBound,
    VermaPBW.lowerVermaProjective⟩

end Langlands.Archimedean
