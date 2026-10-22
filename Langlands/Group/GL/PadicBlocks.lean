import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Padic

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

variable {n : ℕ}

/-- The parabolic topology induced by the supplied field realization. -/
abbrev parabolicTopology (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.parabolic F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The parabolic is a topological group for this exact topology. -/
theorem parabolicTopologicalGroup (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    IsTopologicalGroup (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The parabolic is Hausdorff for this exact topology. -/
theorem parabolicT2Space (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    T2Space (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.generalLinearT2Space n
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

/-- The opposite parabolic topology induced by the supplied field realization. -/
abbrev oppositeParabolicTopology (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.oppositeParabolic F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The opposite parabolic is a topological group for this exact topology. -/
theorem oppositeParabolicTopologicalGroup (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeParabolicTopology B
    IsTopologicalGroup (B.oppositeParabolic F.Carrier) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The opposite parabolic is Hausdorff for this exact topology. -/
theorem oppositeParabolicT2Space (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeParabolicTopology B
    T2Space (B.oppositeParabolic F.Carrier) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The opposite parabolic is locally compact for this exact topology. -/
theorem oppositeParabolicLocallyCompactSpace (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeParabolicTopology B
    LocallyCompactSpace (B.oppositeParabolic F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.oppositeParabolicLocallyCompactSpace F.Carrier

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

/-- The proved parabolic product homeomorphism for the supplied realization. -/
def blockDecomposition (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.parabolic F.Carrier ≃ₜ B.unipotentRadical F.Carrier × B.Levi F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.decompositionHomeomorph F.Carrier

end TopologicalData

/-- Canonical Topology for the actual parabolic, with no supplied realization. -/
noncomputable abbrev canonicalParabolicTopology
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.parabolic F.Carrier) :=
  F.canonicalTopologicalData.parabolicTopology B

/-- Canonical TopologicalGroup for the actual parabolic, with no supplied realization. -/
noncomputable abbrev canonicalParabolicTopologicalGroup
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalParabolicTopology B
    IsTopologicalGroup (B.parabolic F.Carrier) :=
  F.canonicalTopologicalData.parabolicTopologicalGroup B

/-- Canonical T2Space for the actual parabolic, with no supplied realization. -/
noncomputable abbrev canonicalParabolicT2Space
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalParabolicTopology B
    T2Space (B.parabolic F.Carrier) :=
  F.canonicalTopologicalData.parabolicT2Space B

/-- Canonical LocallyCompactSpace for the actual parabolic, with no supplied realization. -/
noncomputable abbrev canonicalParabolicLocallyCompactSpace
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalParabolicTopology B
    LocallyCompactSpace (B.parabolic F.Carrier) :=
  F.canonicalTopologicalData.parabolicLocallyCompactSpace B

/-- Canonical Topology for the actual opposite parabolic, with no supplied realization. -/
noncomputable abbrev canonicalOppositeParabolicTopology
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeParabolicTopology B

/-- Canonical TopologicalGroup for the actual opposite parabolic, with no supplied realization. -/
noncomputable abbrev canonicalOppositeParabolicTopologicalGroup
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeParabolicTopology B
    IsTopologicalGroup (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeParabolicTopologicalGroup B

/-- Canonical T2Space for the actual opposite parabolic, with no supplied realization. -/
noncomputable abbrev canonicalOppositeParabolicT2Space
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeParabolicTopology B
    T2Space (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeParabolicT2Space B

/-- Canonical LocallyCompactSpace for the actual opposite parabolic, with no supplied realization. -/
noncomputable abbrev canonicalOppositeParabolicLocallyCompactSpace
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeParabolicTopology B
    LocallyCompactSpace (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeParabolicLocallyCompactSpace B

/-- Canonical Topology for the actual unipotent radical, with no supplied realization. -/
noncomputable abbrev canonicalUnipotentRadicalTopology
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.unipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.unipotentRadicalTopology B

/-- Canonical TopologicalGroup for the actual unipotent radical, with no supplied realization. -/
noncomputable abbrev canonicalUnipotentRadicalTopologicalGroup
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalUnipotentRadicalTopology B
    IsTopologicalGroup (B.unipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.unipotentRadicalTopologicalGroup B

/-- Canonical T2Space for the actual unipotent radical, with no supplied realization. -/
noncomputable abbrev canonicalUnipotentRadicalT2Space
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalUnipotentRadicalTopology B
    T2Space (B.unipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.unipotentRadicalT2Space B

/-- Canonical LocallyCompactSpace for the actual unipotent radical, with no supplied realization. -/
noncomputable abbrev canonicalUnipotentRadicalLocallyCompactSpace
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalUnipotentRadicalTopology B
    LocallyCompactSpace (B.unipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.unipotentRadicalLocallyCompactSpace B

/-- Canonical Topology for the actual Levi product, with no supplied realization. -/
noncomputable abbrev canonicalLeviTopology
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.leviTopology B

/-- Canonical TopologicalGroup for the actual Levi product, with no supplied realization. -/
noncomputable abbrev canonicalLeviTopologicalGroup
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalLeviTopology B
    IsTopologicalGroup (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.leviTopologicalGroup B

/-- Canonical T2Space for the actual Levi product, with no supplied realization. -/
noncomputable abbrev canonicalLeviT2Space
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalLeviTopology B
    T2Space (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.leviT2Space B

/-- Canonical LocallyCompactSpace for the actual Levi product, with no supplied realization. -/
noncomputable abbrev canonicalLeviLocallyCompactSpace
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalLeviTopology B
    LocallyCompactSpace (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.leviLocallyCompactSpace B

end Langlands.PadicField
