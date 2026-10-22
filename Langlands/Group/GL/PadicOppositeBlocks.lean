import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.GL.PadicBlocks

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

private theorem oppositeFieldT2 (T : F.TopologicalData) :
    letI := T.topology
    T2Space F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  have := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  infer_instance

variable {n : ℕ}

/-- The opposite radical inherits the exact supplied field topology. -/
abbrev oppositeUnipotentRadicalTopology (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.oppositeUnipotentRadical F.Carrier) := by
  letI := T.topology
  infer_instance

/-- The actual opposite radical is a topological group for this topology. -/
theorem oppositeUnipotentRadicalTopologicalGroup (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeUnipotentRadicalTopology B
    IsTopologicalGroup (B.oppositeUnipotentRadical F.Carrier) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  infer_instance

/-- The actual opposite radical is Hausdorff for this topology. -/
theorem oppositeUnipotentRadicalT2Space (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeUnipotentRadicalTopology B
    T2Space (B.oppositeUnipotentRadical F.Carrier) := by
  let := T.topology
  let := T.generalLinearT2Space n
  infer_instance

/-- The actual opposite radical is locally compact by its proved closed inclusion. -/
theorem oppositeUnipotentRadicalLocallyCompactSpace (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeUnipotentRadicalTopology B
    LocallyCompactSpace (B.oppositeUnipotentRadical F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.oppositeFieldT2
  let := T.generalLinearLocallyCompactSpace n
  exact B.oppositeUnipotentRadicalLocallyCompactSpace F.Carrier

/-- The continuous actual lower-block projection into the common Levi. -/
def oppositeBlockLeviProjection (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.oppositeParabolic F.Carrier) (B.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.oppositeLeviProjectionContinuous F.Carrier

/-- The common block diagonal section, valued continuously in the opposite parabolic. -/
def oppositeBlockLeviSection (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ContinuousMonoidHom (B.Levi F.Carrier) (B.oppositeParabolic F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.oppositeLeviInParabolicContinuous F.Carrier

/-- The constructed lower radical-times-Levi homeomorphism for the supplied realization. -/
def oppositeBlockDecomposition (T : F.TopologicalData) (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.oppositeParabolic F.Carrier ≃ₜ B.oppositeUnipotentRadical F.Carrier ×
      B.Levi F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact B.oppositeDecompositionHomeomorph F.Carrier

/-- The common Levi's action on the actual opposite radical is jointly continuous. -/
theorem oppositeBlockLeviActionContinuous (T : F.TopologicalData)
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    Continuous (fun mu : B.Levi F.Carrier × B.oppositeUnipotentRadical F.Carrier =>
      B.oppositeLeviAction F.Carrier mu.1 mu.2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact B.continuous_oppositeLeviAction F.Carrier

end TopologicalData

/-- Canonical topology of the actual opposite radical for every algebraic p-adic field. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalTopology
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    TopologicalSpace (B.oppositeUnipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalTopology B

/-- Canonical group continuity of the actual opposite radical. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalTopologicalGroup
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeUnipotentRadicalTopology B
    IsTopologicalGroup (B.oppositeUnipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalTopologicalGroup B

/-- Canonical Hausdorff property of the actual opposite radical. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalT2Space
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeUnipotentRadicalTopology B
    T2Space (B.oppositeUnipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalT2Space B

/-- Canonical local compactness of the actual opposite radical. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalLocallyCompactSpace
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeUnipotentRadicalTopology B
    LocallyCompactSpace (B.oppositeUnipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalLocallyCompactSpace B

/-- Canonical continuous projection of the opposite parabolic to its common Levi. -/
noncomputable abbrev canonicalOppositeBlockLeviProjection
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalTopologicalData.topology
    ContinuousMonoidHom (B.oppositeParabolic F.Carrier) (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.oppositeBlockLeviProjection B

/-- Canonical continuous block diagonal section into the opposite parabolic. -/
noncomputable abbrev canonicalOppositeBlockLeviSection
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalTopologicalData.topology
    ContinuousMonoidHom (B.Levi F.Carrier) (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeBlockLeviSection B

/-- Canonical lower radical-times-Levi homeomorphism. -/
noncomputable abbrev canonicalOppositeBlockDecomposition
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalTopologicalData.topology
    B.oppositeParabolic F.Carrier ≃ₜ B.oppositeUnipotentRadical F.Carrier ×
      B.Levi F.Carrier :=
  F.canonicalTopologicalData.oppositeBlockDecomposition B

/-- Canonical joint continuity of the Levi action on the opposite radical. -/
noncomputable abbrev canonicalOppositeBlockLeviActionContinuous
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalTopologicalData.topology
    Continuous (fun mu : B.Levi F.Carrier × B.oppositeUnipotentRadical F.Carrier =>
      B.oppositeLeviAction F.Carrier mu.1 mu.2) :=
  F.canonicalTopologicalData.oppositeBlockLeviActionContinuous B

end Langlands.PadicField
