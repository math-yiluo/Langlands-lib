import Langlands.Representation.Archimedean.ComplexJacquetBimoduleBridge
import Langlands.Representation.Archimedean.ComplexJacquetBimoduleReduction

/-!
# Casselman's theorem for `𝔤𝔩_n(ℂ)` from the Bernstein–Gelfand inputs

The six inputs on lower Verma modules of `𝔤𝔩_n(ℂ)` collected in
`VermaGL.BernsteinGelfandInputsStatement` imply `ComplexJacquetModuleFiniteStatement`: for an
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module the Jacquet module `V/𝔫V` is finite-dimensional
and nonzero. The proof chains three implications: the Bernstein–Gelfand reduction
(`complexJacquetBimoduleReduction`), the bridge from bimodules to one-sided nonvanishing
(`complexJacquetOneSided_of_bimodule`), and `complexJacquetModuleFinite_of_oneSided`. See the
paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- The six Bernstein–Gelfand inputs on lower Verma modules of `𝔤𝔩_n(ℂ)` (weight space of the
generator, Duflo's theorem, Kostant's multiplicity lower bound, central characters, the upper
bound for equivariant maps into `End M⁻(λ)` and projectivity of `M⁻(λ)`, for `Z`-extremal `λ`)
imply Casselman's theorem for `(𝔤𝔩_n(ℂ), U(n))`-modules: the Jacquet module `V/𝔫V` of an
irreducible admissible module is finite-dimensional and nonzero. -/
def ComplexJacquetModuleFiniteReductionStatement : Prop :=
  VermaGL.BernsteinGelfandInputsStatement.{uV, uV} → ComplexJacquetModuleFiniteStatement.{uV}

/-- Proof of the reduction: Bernstein–Gelfand reduction, then the bimodule bridge, then the
one-sided criterion. -/
theorem complexJacquetModuleFiniteReduction :
    ComplexJacquetModuleFiniteReductionStatement.{uV} :=
  fun h => complexJacquetModuleFinite_of_oneSided
    (complexJacquetOneSided_of_bimodule (complexJacquetBimoduleReduction h))

end Langlands.Archimedean
