import Langlands.Group.GL.Basic
import Langlands.LocalField.Canonical
import Langlands.LocalField.Topology

/-!
# General linear groups over every finite p-adic extension

These explicit structures install the topology of a supplied `TopologicalData`
on the actual matrix unit group. The canonical specialization needs only the
algebraic `PadicField`.
-/

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

/-- The matrix unit topology associated to a supplied realization of the field. -/
abbrev generalLinearTopology (T : F.TopologicalData) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact inferInstance

/-- Multiplication and inversion are continuous for the selected topology. -/
theorem generalLinearTopologicalGroup (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    IsTopologicalGroup (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact inferInstance

/-- The selected matrix unit topology is Hausdorff. -/
theorem generalLinearT2Space (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    T2Space (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.fieldT2
  exact inferInstance

/-- The selected matrix unit topology is locally compact. -/
theorem generalLinearLocallyCompactSpace (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    LocallyCompactSpace (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F.Carrier))
  exact inferInstance

/-- The continuous determinant for the selected field realization. -/
def generalLinearDeterminant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier) F.Carrierˣ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact GeneralLinear.determinantContinuous

/-- The continuous scalar homomorphism for the selected field realization. -/
def generalLinearScalar (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom F.Carrierˣ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  exact GeneralLinear.scalarContinuous

end TopologicalData

/-- The canonical topology on actual `GL_n(F)`, for every algebraic p-adic field. -/
noncomputable abbrev canonicalGeneralLinearTopology (F : PadicField.{u} p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopology n

/-- The canonical topological group structure, requiring no supplied realization. -/
noncomputable abbrev canonicalGeneralLinearTopologicalGroup (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

/-- Hausdorffness for the canonical topology on actual `GL_n(F)`. -/
noncomputable abbrev canonicalGeneralLinearT2Space (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearT2Space n

/-- Local compactness for the canonical topology on actual `GL_n(F)`. -/
noncomputable abbrev canonicalGeneralLinearLocallyCompactSpace
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n

end Langlands.PadicField
