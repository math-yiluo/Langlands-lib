import Langlands.HarmonicAnalysis.Conductor

/-! A focused plus-sign Fourier integral of one actual p-adic lattice coset. -/

namespace Langlands.HarmonicAnalysis

open MeasureTheory

universe u

/-- For every unitary additive character `ψ` with conductor `n`, every regular
additive Haar measure `μ`, level `m`, centre `a` and argument `y`, the raw
characteristic function of the coset `a + π^(-m) O` has a convergent plus-sign
Fourier integrand at `y`, and its Bochner Fourier integral at `y` is
`μ(π^(-m) O) * ψ(a*y)` times the characteristic function of `π^(-(n-m)) O`. -/
def PadicLatticeFourierStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (m : ℤ) (a y : F.Carrier),
    let C : Set F.Carrier := {x | x - a ∈ T.additiveLattice m}
    let indicatorC : F.Carrier → ℂ := C.indicator (fun _ => (1 : ℂ))
    Integrable (fun x => ψ.complex (x * y) * indicatorC x) μ.measure ∧
    fourierIntegral ψ μ indicatorC y =
      ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) *
        ψ.complex (a * y) *
        (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y

end Langlands.HarmonicAnalysis
