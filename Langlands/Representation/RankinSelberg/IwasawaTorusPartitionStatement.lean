import Langlands.LocalField.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurable uniformizer-coset partition of the diagonal torus

This is an internal measurable partition of the diagonal torus into the
uniformizer cosets of its integral units, with normalized product Haar mass
one on every coset. It assumes no partition, Haar decomposition or quotient
measure. This module does not prove the statement.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear

universe uF

/-- The diagonal torus is the disjoint union, over all exponent vectors, of the
measurable cosets `t(lam) * U` of the integral units. Every coset is the
translate of the normalized product Haar measure on `U` and has mass one. -/
def IwasawaTorusPartitionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (m : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrierˣ
  letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
  ∀ ϖ : F.Carrierˣ,
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
  let A := Fin m → F.Carrierˣ
  let O := (ValuativeRel.valuation F.Carrier).integer
  let da : Measure A := Measure.pi (fun _ : Fin m =>
    localMultiplicativeHaar F.Carrier)
  let U : Set A := {u : A | ∀ i, u i ∈ integralUnits O}
  let t : (Fin m → ℤ) → A := fun lam i => ϖ ^ lam i
  let C : (Fin m → ℤ) → Set A := fun lam => (fun u : A => t lam * u) '' U
  MeasurableSet U ∧ da U = 1 ∧
    (∀ lam : Fin m → ℤ, MeasurableSet (C lam) ∧ da (C lam) = 1 ∧
      Measure.map (fun u : A => t lam * u) (da.restrict U) = da.restrict (C lam)) ∧
    Pairwise (fun lam lam' : Fin m → ℤ => Disjoint (C lam) (C lam')) ∧
    (⋃ lam : Fin m → ℤ, C lam) = Set.univ

end Langlands.RankinSelberg
