import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.Padic

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

/-- The full upper unipotent subgroup topology for the supplied realization. -/
abbrev upperUnipotentTopology (T : F.TopologicalData) (n : ℕ) :
    TopologicalSpace (GeneralLinear.upperUnipotent n F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The upper unipotent subgroup is a topological group. -/
theorem upperUnipotentTopologicalGroup (T : F.TopologicalData) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    IsTopologicalGroup (GeneralLinear.upperUnipotent n F.Carrier) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The upper unipotent subgroup is Hausdorff. -/
theorem upperUnipotentT2Space (T : F.TopologicalData) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    T2Space (GeneralLinear.upperUnipotent n F.Carrier) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The upper unipotent subgroup is locally compact by its proved closedness. -/
theorem upperUnipotentLocallyCompactSpace (T : F.TopologicalData) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    LocallyCompactSpace (GeneralLinear.upperUnipotent n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact GeneralLinear.UpperUnipotent.locallyCompactSpace

/-- The continuous adjacent-entry sum for every supplied p-adic realization. -/
def upperUnipotentSum (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
      (Multiplicative F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.UpperUnipotent.superdiagonalSumContinuous

end TopologicalData

/-- Canonical Topology for the full upper unipotent matrix group. -/
noncomputable abbrev canonicalUpperUnipotentTopology (F : PadicField.{u} p) (n : ℕ) :
    TopologicalSpace (GeneralLinear.upperUnipotent n F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentTopology n

/-- Canonical TopologicalGroup for the full upper unipotent matrix group. -/
noncomputable abbrev canonicalUpperUnipotentTopologicalGroup (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalUpperUnipotentTopology n
    IsTopologicalGroup (GeneralLinear.upperUnipotent n F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentTopologicalGroup n

/-- Canonical T2Space for the full upper unipotent matrix group. -/
noncomputable abbrev canonicalUpperUnipotentT2Space (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalUpperUnipotentTopology n
    T2Space (GeneralLinear.upperUnipotent n F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentT2Space n

/-- Canonical LocallyCompactSpace for the full upper unipotent matrix group. -/
noncomputable abbrev canonicalUpperUnipotentLocallyCompactSpace (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalUpperUnipotentTopology n
    LocallyCompactSpace (GeneralLinear.upperUnipotent n F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace n

end Langlands.PadicField
