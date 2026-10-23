import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.Maps

/-!
# Symmetries of the normalized general linear Haar measure

A statement about the existing measure and actual matrix-group maps.
-/

namespace Langlands.RankinSelberg

open MeasureTheory

universe uF

/-- The normalized Haar measure on positive-rank general linear groups is
invariant under inversion, inverse transpose, transpose, and conjugation. -/
def GeneralLinearHaarSymmetriesStatement
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] : Prop :=
  let μ := generalLinearHaar F n
  Measure.IsInvInvariant μ ∧
    MeasurePreserving (GeneralLinear.inverseTranspose (n + 1) F) μ μ ∧
    MeasurePreserving
      (fun g : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
        GeneralLinear.inverseTranspose (n + 1) F g⁻¹) μ μ ∧
    ∀ a : Matrix.GeneralLinearGroup (Fin (n + 1)) F,
      MeasurePreserving (fun g => a * g * a⁻¹) μ μ

end Langlands.RankinSelberg
