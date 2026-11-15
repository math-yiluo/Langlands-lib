import Langlands.Representation.Archimedean.BGChaseConclusion

/-!
# The Bernstein–Gelfand inputs imply one-sided nonvanishing for bimodules

The six inputs on lower Verma modules of `𝔤𝔩_n(ℂ)` collected in
`VermaGL.BernsteinGelfandInputsStatement` imply `ComplexJacquetBimoduleStatement`
(Bernstein–Gelfand 1980, Theorem 5.9, proof in 5.10). See the paired Markdown and the
`BGChase*` modules.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- The six Bernstein–Gelfand inputs on lower Verma modules of `𝔤𝔩_n(ℂ)` (weight space of the
generator, Duflo's theorem, Kostant's multiplicity lower bound, central characters, the upper
bound for equivariant maps into `End M⁻(λ)` and projectivity of `M⁻(λ)`, for `Z`-extremal `λ`)
imply one-sided nonvanishing for Harish-Chandra bimodules of `𝔤𝔩_n(ℂ)`
(Bernstein–Gelfand 1980, Theorem 5.9, proof in 5.10). -/
def ComplexJacquetBimoduleReductionStatement : Prop :=
  VermaGL.BernsteinGelfandInputsStatement.{uV, uV} → ComplexJacquetBimoduleStatement.{uV}

/-- Proof of the reduction: the Bernstein–Gelfand chase of the `BGChase*` modules. -/
theorem complexJacquetBimoduleReduction : ComplexJacquetBimoduleReductionStatement.{uV} :=
  fun ⟨hWt, hDuflo, hK, hCC, hB, hP⟩ =>
    BGChase.complexJacquetBimodule_of_inputs hWt hDuflo hK hCC hB hP

end Langlands.Archimedean
