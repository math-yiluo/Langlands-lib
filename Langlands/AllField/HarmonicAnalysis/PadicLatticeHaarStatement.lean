import Langlands.HarmonicAnalysis.PadicLatticeHaarStatement
import Langlands.AllField.HarmonicAnalysis.Conductor
/-! Valuation-lattice Haar masses and a conductor-normalized Haar measure for each
supplied local-field topology, stated without any Fourier or self-duality hypothesis. -/

open scoped ENNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeHaarStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- For the supplied local-field topology, write `L m = π^(-m) O` for the valuation
lattice `T.additiveLattice m` and `q` for the residue cardinality.

* Every regular additive Haar measure gives each `L m`, for every integer `m`,
  a finite mass whose real value is positive and equals `q ^ m` times the
  real mass of `L 0 = O`.
* For every continuous nontrivial unitary additive character `ψ` of conductor
  `n`, some regular additive Haar measure gives each `L m` the real mass
  `q ^ m / √(q ^ n)`, so the masses of `L m` and `L (n - m)` are reciprocal.

Powers are integer powers, and no self-duality is asserted. -/
def PadicLatticeHaarStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  (∀ (μ : AdditiveHaarMeasure F) (m : ℤ),
    μ.measure (T.additiveLattice m : Set F) < ∞ ∧
    0 < (μ.measure (T.additiveLattice m : Set F)).toReal ∧
    (μ.measure (T.additiveLattice m : Set F)).toReal =
      (T.residueCardinality : ℝ) ^ m *
        (μ.measure (T.additiveLattice 0 : Set F)).toReal) ∧
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∃ ν : AdditiveHaarMeasure F, ∀ m : ℤ,
      (ν.measure (T.additiveLattice m : Set F)).toReal =
        (T.residueCardinality : ℝ) ^ m /
          Real.sqrt ((T.residueCardinality : ℝ) ^ T.additiveConductor ψ) ∧
      (ν.measure (T.additiveLattice m : Set F)).toReal *
        (ν.measure
          (T.additiveLattice (T.additiveConductor ψ - m) : Set F)).toReal = 1

end Langlands.AllField.HarmonicAnalysis
