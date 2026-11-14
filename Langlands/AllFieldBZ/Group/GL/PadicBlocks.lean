import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.Group.GL.PadicBlocks

/-!
# All-field port of `Langlands.Group.GL.PadicBlocks`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.PadicBlocks` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable {F : LocalFieldPackage.{u}}

namespace TopologicalData
variable {n : ℕ}

/-- The parabolic topology induced by the supplied field realization. -/
abbrev parabolicTopology (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.parabolic F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The parabolic is locally compact for this exact topology. -/
theorem parabolicLocallyCompactSpace (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    LocallyCompactSpace (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.parabolicLocallyCompactSpace F.Carrier

/-- The unipotent radical topology induced by the supplied field realization. -/
abbrev unipotentRadicalTopology (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.unipotentRadical F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The unipotent radical is a topological group for this exact topology. -/
theorem unipotentRadicalTopologicalGroup (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    IsTopologicalGroup (B.unipotentRadical F.Carrier) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The unipotent radical is Hausdorff for this exact topology. -/
theorem unipotentRadicalT2Space (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    T2Space (B.unipotentRadical F.Carrier) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The unipotent radical is locally compact for this exact topology. -/
theorem unipotentRadicalLocallyCompactSpace (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    LocallyCompactSpace (B.unipotentRadical F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.unipotentRadicalLocallyCompactSpace F.Carrier

/-- The Levi product topology induced by the supplied field realization. -/
abbrev leviTopology (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.Levi F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The Levi product is a topological group for this exact topology. -/
theorem leviTopologicalGroup (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    IsTopologicalGroup (B.Levi F.Carrier) := by
  let := T.topology
  have : ∀ i : Fin B.length,
      IsTopologicalGroup (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearTopologicalGroup (B.size i)
  infer_instance

/-- The Levi product is Hausdorff for this exact topology. -/
theorem leviT2Space (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    T2Space (B.Levi F.Carrier) := by
  let := T.topology
  have : ∀ i : Fin B.length, T2Space (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearT2Space (B.size i)
  infer_instance

/-- The Levi product is locally compact for this exact topology. -/
theorem leviLocallyCompactSpace (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    LocallyCompactSpace (B.Levi F.Carrier) := by
  let := T.topology
  have : ∀ i : Fin B.length,
      LocallyCompactSpace (GeneralLinear (B.size i) F.Carrier) :=
    fun i => T.generalLinearLocallyCompactSpace (B.size i)
  infer_instance

/-- The continuous Levi embedding for every supplied p-adic field realization. -/
def blockLeviEmbedding (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.Levi F.Carrier) (GeneralLinear n F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.leviEmbeddingContinuous F.Carrier

/-- The continuous Levi projection for every supplied p-adic field realization. -/
def blockLeviProjection (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.parabolic F.Carrier) (B.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.leviProjectionContinuous F.Carrier

end TopologicalData
end Langlands.AllFieldBZ.LocalFieldPackage
