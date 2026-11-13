import Langlands.HarmonicAnalysis.PadicLatticeFourierStatement
import Langlands.AllField.HarmonicAnalysis.Conductor
/-! A focused plus-sign Fourier integral of one actual local-field lattice coset. -/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement
open Langlands.AllField.HarmonicAnalysis

open MeasureTheory

universe u

/-- For every unitary additive character `ψ` with conductor `n`, every regular
additive Haar measure `μ`, level `m`, centre `a` and argument `y`, the raw
characteristic function of the coset `a + π^(-m) O` has a convergent plus-sign
Fourier integrand at `y`, and its Bochner Fourier integral at `y` is
`μ(π^(-m) O) * ψ(a*y)` times the characteristic function of `π^(-(n-m)) O`. -/
def PadicLatticeFourierStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (m : ℤ) (a y : F),
    let C : Set F := {x | x - a ∈ T.additiveLattice m}
    let indicatorC : F → ℂ := C.indicator (fun _ => (1 : ℂ))
    Integrable (fun x => ψ.complex (x * y) * indicatorC x) μ.measure ∧
    fourierIntegral ψ μ indicatorC y =
      ((μ.measure (T.additiveLattice m : Set F)).toReal : ℂ) *
        ψ.complex (a * y) *
        (T.additiveLattice (T.additiveConductor ψ - m) : Set F).indicator
          (fun _ => (1 : ℂ)) y

end Langlands.AllField.HarmonicAnalysis
