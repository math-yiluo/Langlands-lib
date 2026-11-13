import Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Measurable uniformizer-coset partition of the diagonal torus

This is an internal measurable partition of the diagonal torus into the
uniformizer cosets of its integral units, with normalized product Haar mass
one on every coset. It assumes no partition, Haar decomposition or quotient
measure. This module does not prove the statement.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding IwasawaTorusPartitionStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear

universe uF

/-- The diagonal torus is the disjoint union, over all exponent vectors, of the
measurable cosets `t(lam) * U` of the integral units. Every coset is the
translate of the normalized product Haar measure on `U` and has mass one. -/
def IwasawaTorusPartitionStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (m : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel Fˣ
  letI : BorelSpace Fˣ := ⟨rfl⟩
  ∀ ϖ : Fˣ,
    Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ →
  let A := Fin m → Fˣ
  let O := (ValuativeRel.valuation F).integer
  let da : Measure A := Measure.pi (fun _ : Fin m =>
    localMultiplicativeHaar F)
  let U : Set A := {u : A | ∀ i, u i ∈ integralUnits O}
  let t : (Fin m → ℤ) → A := fun lam i => ϖ ^ lam i
  let C : (Fin m → ℤ) → Set A := fun lam => (fun u : A => t lam * u) '' U
  MeasurableSet U ∧ da U = 1 ∧
    (∀ lam : Fin m → ℤ, MeasurableSet (C lam) ∧ da (C lam) = 1 ∧
      Measure.map (fun u : A => t lam * u) (da.restrict U) = da.restrict (C lam)) ∧
    Pairwise (fun lam lam' : Fin m → ℤ => Disjoint (C lam) (C lam')) ∧
    (⋃ lam : Fin m → ℤ, C lam) = Set.univ

end Langlands.AllField.RankinSelberg
