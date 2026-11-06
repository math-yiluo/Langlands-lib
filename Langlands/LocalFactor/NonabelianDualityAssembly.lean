import Langlands.LocalFactor.CommonClosureDualityInduction
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof

/-!
# Reduction of actual duality to character lines and degree-zero generation

Self-dual Haar existence supplies the larger-field measures needed in the
induced-generator argument. The rank-one equation and actual generation
remain explicit premises of the assembly theorem.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

/-- The fixed-Haar equation restricted to actual continuous character lines.
This isolates the rank-one input; it does not assert that input is proved. -/
def CharacterLineDualityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F)
    (hε : IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E),
    FourierDualMeasures F E ψ μ μ' →
    ∀ χ : weilSubgroup F E →ₜ* ℂˣ,
      ExactGrothendieckGroup.characterClass χ ∈
        dualityKernel F ε hε.2.1 E ψ μ μ'

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The proved scalar self-dual measure theorem supplies a Fourier-dual
pair on every actual common-closure intermediate field. -/
theorem exists_fourierDualMeasures (E : Extension F) (ψ : AdditiveCharacter F E) :
    ∃ μ : HaarMeasure F E, FourierDualMeasures F E ψ μ μ := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  obtain ⟨htd, h⟩ :=
    HarmonicAnalysis.padicSelfDualMeasureExists
      (E.asPadicField (p := p)) (fieldData F E)
  let := htd
  exact h ψ

/-- Character-line duality over all intermediate fields puts every displayed
induced character difference in the base field's duality kernel. -/
theorem characterDifferenceGenerators_mem_dualityKernel
    (hline : CharacterLineDualityStatement.{uF, uV})
    (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F) (hε : IsSystem F e ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E) :
    characterDifferenceInductionGenerators.{uF, uV} F E ⊆
      dualityKernel F ε hε.2.1 E ψ μ μ' := by
  rintro y ⟨L, h, χ, χ', rfl⟩
  obtain ⟨ν, hν⟩ := exists_fourierDualMeasures F L (traceCharacter F E L h ψ)
  have hχ := hline F e ε hε L (traceCharacter F E L h ψ) ν ν hν χ
  have hχ' := hline F e ε hε L (traceCharacter F E L h ψ) ν ν hν χ'
  let z : DegreeZero.{uF, uV} F L :=
    ⟨ExactGrothendieckGroup.characterClass χ -
      ExactGrothendieckGroup.characterClass χ', by
        change degree F L _ = 0
        rw [map_sub, ExactGrothendieckGroup.degree_characterClass,
          ExactGrothendieckGroup.degree_characterClass, sub_self]⟩
  have hz : z.val ∈
      dualityKernel F ε hε.2.1 L (traceCharacter F E L h ψ) ν ν :=
    (dualityKernel F ε hε.2.1 L (traceCharacter F E L h ψ) ν ν).sub_mem hχ hχ'
  change dualityDefect F ε hε.2.1 E ψ μ μ' (induce F E L h z.val) = 0
  rw [dualityDefect_induce F e ε hε E L h ψ μ μ' ν ν z]
  exact hz

/-- Actual degree-zero generation and the rank-one equation imply the
unchanged fixed-Haar functional equation. Neither input is hidden. -/
theorem fixedHaarDuality_of_generation_of_characterLineDuality
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV})
    (hline : CharacterLineDualityStatement.{uF, uV}) :
    FixedHaarDualityStatement.{uF, uV} := by
  intro p hp F e ε hε E
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ μ μ' hμ x
  have htop := dualityKernel_eq_top_of_commonClosureDegreeZeroGeneration F
    (hgen p F) ε hε.2.1 E ψ μ μ'
    (hline F e ε hε E ψ μ μ' hμ 1)
    (characterDifferenceGenerators_mem_dualityKernel F hline e ε hε E ψ μ μ')
  have hx : x ∈ dualityKernel F ε hε.2.1 E ψ μ μ' := by
    rw [htop]
    exact Submodule.mem_top
  exact (mem_dualityKernel F ε hε.2.1 E ψ μ μ' x).mp hx

/-- The two explicit inputs also imply the unchanged aggregate statement,
using the proved reduction from fixed-Haar to spectral duality. -/
theorem dualFunctionalEquation_of_generation_of_characterLineDuality
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV})
    (hline : CharacterLineDualityStatement.{uF, uV}) :
    DualFunctionalEquationStatement.{uF, uV} :=
  dualFunctionalEquation_of_fixedHaarDuality
    (fixedHaarDuality_of_generation_of_characterLineDuality hgen hline)

end Langlands.LocalFactor.NonabelianSystem
