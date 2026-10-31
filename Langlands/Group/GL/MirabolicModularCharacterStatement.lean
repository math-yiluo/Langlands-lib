import Langlands.Group.GL.Mirabolic
import Langlands.Group.GL.NormalizedCharacter
import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# The modular character of the actual mirabolic group

Bernstein--Zelevinsky (1977, §4.2) record that the modular function of the
mirabolic subgroup `P_(n+1) ≤ GL_(n+1)(F)` is the restriction of `ν⁻¹`, where
`ν(g) = |det g|`. In their convention `Δ_G = mod_G⁻¹`, while Mathlib's
`MeasureTheory.Measure.modularCharacter` is the right-translation scalar
`map (· * g) μ = Δ(g) • μ` of a left Haar measure `μ`, that is BZ77's `mod_G`.
This proposition therefore states that Mathlib's modular character of the actual
mirabolic group equals the positive residue-normalized determinant norm. It is a
proposition definition, not a proof.
-/

namespace Langlands

universe uF

open scoped NNReal

/-- For the supplied realization `T` and every rank `n`, Mathlib's Haar-defined modular
character of the actual mirabolic subgroup `P_(n+1) ≤ GL_(n+1)(F)`, with the subspace
topology induced from `T`, is `g ↦ |det g|`, the residue-normalized determinant norm
`T.determinantNorm (n + 1)` restricted to `P_(n+1)`. -/
def MirabolicModularCharacterStatement {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  haveI := T.fieldT2
  ∀ n : ℕ,
    haveI := T.generalLinearTopologicalGroup (n + 1)
    haveI := T.generalLinearLocallyCompactSpace (n + 1)
    haveI := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
    ∀ g : GeneralLinear.mirabolic n F.Carrier,
      MeasureTheory.Measure.modularCharacter g =
        ((T.determinantNorm (n + 1) g.val : ℝ≥0ˣ) : ℝ≥0)

end Langlands
