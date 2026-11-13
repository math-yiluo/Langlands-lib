import Langlands.Group.GL.PadicBlocks
import Langlands.AllField.Group.GL.Padic
namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

variable {n : ℕ}

/-- The unipotent radical topology induced by the supplied field realization. -/
abbrev unipotentRadicalTopology (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.unipotentRadical F) := by
  letI := T.topology
  infer_instance

/-- The unipotent radical is a topological group for this exact topology. -/
theorem unipotentRadicalTopologicalGroup (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    IsTopologicalGroup (B.unipotentRadical F) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The unipotent radical is Hausdorff for this exact topology. -/
theorem unipotentRadicalT2Space (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    T2Space (B.unipotentRadical F) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The unipotent radical is locally compact for this exact topology. -/
theorem unipotentRadicalLocallyCompactSpace (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    LocallyCompactSpace (B.unipotentRadical F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.unipotentRadicalLocallyCompactSpace F

/-- The Levi product topology induced by the supplied field realization. -/
abbrev leviTopology (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.Levi F) := by
  letI := T.topology
  infer_instance

/-- The Levi product is a topological group for this exact topology. -/
theorem leviTopologicalGroup (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    IsTopologicalGroup (B.Levi F) := by
  let := T.topology
  have : ∀ i : Fin B.length,
      IsTopologicalGroup (GeneralLinear (B.size i) F) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  infer_instance

/-- The Levi product is Hausdorff for this exact topology. -/
theorem leviT2Space (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    T2Space (B.Levi F) := by
  let := T.topology
  have : ∀ i : Fin B.length, T2Space (GeneralLinear (B.size i) F) :=
    fun i => T.generalLinearT2Space (B.size i)
  infer_instance

/-- The Levi product is locally compact for this exact topology. -/
theorem leviLocallyCompactSpace (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    LocallyCompactSpace (B.Levi F) := by
  let := T.topology
  have : ∀ i : Fin B.length,
      LocallyCompactSpace (GeneralLinear (B.size i) F) :=
    fun i => T.generalLinearLocallyCompactSpace (B.size i)
  infer_instance

/-- The continuous Levi embedding for every supplied local-field realization. -/
def blockLeviEmbedding (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.Levi F) (GeneralLinear n F) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.leviEmbeddingContinuous F

/-- The continuous Levi projection for every supplied local-field realization. -/
def blockLeviProjection (T : LocalFieldData F) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.parabolic F) (B.Levi F) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.leviProjectionContinuous F

end LocalFieldData

end Langlands
