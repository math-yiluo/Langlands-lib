import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.PadicBlocks
import Langlands.Group.GL.PadicOppositeBlocks
import Langlands.Group.GL.PadicUpperUnipotent
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-!
# Compact open subgroups for actual p-adic matrix groups
-/

open Filter Topology

namespace Langlands.PadicField

universe u

private theorem inducedNonarchimedean {G H : Type*}
    [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : H →* G) (hf : IsInducing f) : NonarchimedeanGroup H where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean V (by simpa using hV)
    exact ⟨OpenSubgroup.comap f hf.continuous L, fun x hx => hVU (hL hx)⟩

private noncomputable def chooseCompactOpen (G : Type*)
    [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
    {L : OpenSubgroup G // IsCompact (L : Set G) ∧ (L : Set G) ⊆ U} :=
  ⟨Classical.choose (Langlands.compactOpenSubgroupBasis G U hU),
    Classical.choose_spec (Langlands.compactOpenSubgroupBasis G U hU)⟩

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

namespace TopologicalData

/-- The actual GL topology from any supplied p-adic realization is nonarchimedean. -/
theorem generalLinearNonarchimedean (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    NonarchimedeanGroup (GeneralLinear n F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact Langlands.valuativeGeneralLinearNonarchimedean F.Carrier n

/-- The actual upper block parabolic is nonarchimedean in the supplied topology. -/
theorem parabolicNonarchimedean (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    NonarchimedeanGroup (B.parabolic F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  exact inducedNonarchimedean (B.parabolic F.Carrier).subtype .subtypeVal

/-- The actual opposite block parabolic is nonarchimedean in the supplied topology. -/
theorem oppositeParabolicNonarchimedean (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeParabolicTopology B
    NonarchimedeanGroup (B.oppositeParabolic F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  exact inducedNonarchimedean (B.oppositeParabolic F.Carrier).subtype .subtypeVal

/-- The actual block unipotent radical is nonarchimedean in the supplied topology. -/
theorem unipotentRadicalNonarchimedean (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    NonarchimedeanGroup (B.unipotentRadical F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  let := T.parabolicNonarchimedean B
  exact inducedNonarchimedean (B.unipotentRadical F.Carrier).subtype .subtypeVal

/-- The actual opposite unipotent radical is nonarchimedean in the supplied topology. -/
theorem oppositeUnipotentRadicalNonarchimedean (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeUnipotentRadicalTopology B
    NonarchimedeanGroup (B.oppositeUnipotentRadical F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  let := T.oppositeParabolicNonarchimedean B
  exact inducedNonarchimedean (B.oppositeUnipotentRadical F.Carrier).subtype .subtypeVal

/-- The actual product Levi is nonarchimedean in the supplied topology. -/
theorem leviNonarchimedean (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    NonarchimedeanGroup (B.Levi F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  let := inducedNonarchimedean (B.leviSubgroup F.Carrier).subtype .subtypeVal
  exact inducedNonarchimedean (B.leviEquivContinuous F.Carrier).toMonoidHom
    (B.leviEquivContinuous F.Carrier).toHomeomorph.isInducing

/-- The full upper unipotent subgroup is nonarchimedean in the supplied topology. -/
theorem upperUnipotentNonarchimedean (T : F.TopologicalData) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    NonarchimedeanGroup (GeneralLinear.upperUnipotent n F.Carrier) := by
  let := T.topology
  let := T.generalLinearNonarchimedean n
  exact inducedNonarchimedean (GeneralLinear.upperUnipotent n F.Carrier).subtype .subtypeVal

/-- Choose an actual compact open subgroup inside a GL identity neighborhood. -/
noncomputable def generalLinearCompactOpen (T : F.TopologicalData) (n : ℕ) :
    letI := T.generalLinearTopology n
    (U : Set (GeneralLinear n F.Carrier)) → U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      {L : OpenSubgroup (GeneralLinear n F.Carrier) //
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧
          (L : Set (GeneralLinear n F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.generalLinearNonarchimedean n
  letI := T.generalLinearLocallyCompactSpace n
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the upper block parabolic. -/
noncomputable def parabolicCompactOpen (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    (U : Set (B.parabolic F.Carrier)) → U ∈ 𝓝 (1 : B.parabolic F.Carrier) →
      {L : OpenSubgroup (B.parabolic F.Carrier) //
        IsCompact (L : Set (B.parabolic F.Carrier)) ∧ (L : Set (B.parabolic F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.parabolicNonarchimedean B
  letI := T.parabolicLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the opposite block parabolic. -/
noncomputable def oppositeParabolicCompactOpen (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeParabolicTopology B
    (U : Set (B.oppositeParabolic F.Carrier)) → U ∈ 𝓝 (1 : B.oppositeParabolic F.Carrier) →
      {L : OpenSubgroup (B.oppositeParabolic F.Carrier) //
        IsCompact (L : Set (B.oppositeParabolic F.Carrier)) ∧ (L : Set (B.oppositeParabolic F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.oppositeParabolicNonarchimedean B
  letI := T.oppositeParabolicLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the block unipotent radical. -/
noncomputable def unipotentRadicalCompactOpen (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    (U : Set (B.unipotentRadical F.Carrier)) → U ∈ 𝓝 (1 : B.unipotentRadical F.Carrier) →
      {L : OpenSubgroup (B.unipotentRadical F.Carrier) //
        IsCompact (L : Set (B.unipotentRadical F.Carrier)) ∧ (L : Set (B.unipotentRadical F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.unipotentRadicalNonarchimedean B
  letI := T.unipotentRadicalLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the opposite radical. -/
noncomputable def oppositeUnipotentRadicalCompactOpen (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.oppositeUnipotentRadicalTopology B
    (U : Set (B.oppositeUnipotentRadical F.Carrier)) →
      U ∈ 𝓝 (1 : B.oppositeUnipotentRadical F.Carrier) →
        {L : OpenSubgroup (B.oppositeUnipotentRadical F.Carrier) //
          IsCompact (L : Set (B.oppositeUnipotentRadical F.Carrier)) ∧
            (L : Set (B.oppositeUnipotentRadical F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.oppositeUnipotentRadicalNonarchimedean B
  letI := T.oppositeUnipotentRadicalLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the product Levi. -/
noncomputable def leviCompactOpen (T : F.TopologicalData) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    (U : Set (B.Levi F.Carrier)) → U ∈ 𝓝 (1 : B.Levi F.Carrier) →
      {L : OpenSubgroup (B.Levi F.Carrier) //
        IsCompact (L : Set (B.Levi F.Carrier)) ∧ (L : Set (B.Levi F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.leviNonarchimedean B
  letI := T.leviLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an upper-unipotent identity neighborhood. -/
noncomputable def upperUnipotentCompactOpen (T : F.TopologicalData) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    (U : Set (GeneralLinear.upperUnipotent n F.Carrier)) →
      U ∈ 𝓝 (1 : GeneralLinear.upperUnipotent n F.Carrier) →
        {L : OpenSubgroup (GeneralLinear.upperUnipotent n F.Carrier) //
          IsCompact (L : Set (GeneralLinear.upperUnipotent n F.Carrier)) ∧
            (L : Set (GeneralLinear.upperUnipotent n F.Carrier)) ⊆ U} := by
  letI := T.topology
  letI := T.upperUnipotentNonarchimedean n
  letI := T.upperUnipotentLocallyCompactSpace n
  exact chooseCompactOpen _

end TopologicalData

/-- Canonical nonarchimedean certificate for the actual GL. -/
noncomputable abbrev canonicalGeneralLinearNonarchimedean
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    NonarchimedeanGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearNonarchimedean n

/-- Canonically realized compact open subgroups in every identity neighborhood of the GL. -/
noncomputable abbrev canonicalGeneralLinearCompactOpen
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    (U : Set (GeneralLinear n F.Carrier)) → U ∈ 𝓝 (1 : GeneralLinear n F.Carrier) →
      {L : OpenSubgroup (GeneralLinear n F.Carrier) //
        IsCompact (L : Set (GeneralLinear n F.Carrier)) ∧ (L : Set (GeneralLinear n F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.generalLinearCompactOpen n

/-- Canonical nonarchimedean certificate for the actual upper block parabolic. -/
noncomputable abbrev canonicalParabolicNonarchimedean
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalParabolicTopology B
    NonarchimedeanGroup (B.parabolic F.Carrier) :=
  F.canonicalTopologicalData.parabolicNonarchimedean B

/-- Canonically realized compact open subgroups in every identity neighborhood of the upper block parabolic. -/
noncomputable abbrev canonicalParabolicCompactOpen
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalParabolicTopology B
    (U : Set (B.parabolic F.Carrier)) → U ∈ 𝓝 (1 : B.parabolic F.Carrier) →
      {L : OpenSubgroup (B.parabolic F.Carrier) //
        IsCompact (L : Set (B.parabolic F.Carrier)) ∧ (L : Set (B.parabolic F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.parabolicCompactOpen B

/-- Canonical nonarchimedean certificate for the actual opposite block parabolic. -/
noncomputable abbrev canonicalOppositeParabolicNonarchimedean
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeParabolicTopology B
    NonarchimedeanGroup (B.oppositeParabolic F.Carrier) :=
  F.canonicalTopologicalData.oppositeParabolicNonarchimedean B

/-- Canonically realized compact open subgroups in every identity neighborhood of the opposite block parabolic. -/
noncomputable abbrev canonicalOppositeParabolicCompactOpen
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeParabolicTopology B
    (U : Set (B.oppositeParabolic F.Carrier)) → U ∈ 𝓝 (1 : B.oppositeParabolic F.Carrier) →
      {L : OpenSubgroup (B.oppositeParabolic F.Carrier) //
        IsCompact (L : Set (B.oppositeParabolic F.Carrier)) ∧ (L : Set (B.oppositeParabolic F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.oppositeParabolicCompactOpen B

/-- Canonical nonarchimedean certificate for the actual block unipotent radical. -/
noncomputable abbrev canonicalUnipotentRadicalNonarchimedean
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalUnipotentRadicalTopology B
    NonarchimedeanGroup (B.unipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.unipotentRadicalNonarchimedean B

/-- Canonically realized compact open subgroups in every identity neighborhood of the block unipotent radical. -/
noncomputable abbrev canonicalUnipotentRadicalCompactOpen
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalUnipotentRadicalTopology B
    (U : Set (B.unipotentRadical F.Carrier)) → U ∈ 𝓝 (1 : B.unipotentRadical F.Carrier) →
      {L : OpenSubgroup (B.unipotentRadical F.Carrier) //
        IsCompact (L : Set (B.unipotentRadical F.Carrier)) ∧ (L : Set (B.unipotentRadical F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.unipotentRadicalCompactOpen B

/-- Canonical nonarchimedean certificate for the actual opposite radical. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalNonarchimedean
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeUnipotentRadicalTopology B
    NonarchimedeanGroup (B.oppositeUnipotentRadical F.Carrier) :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalNonarchimedean B

/-- Canonically realized compact open subgroups in every opposite-radical identity neighborhood. -/
noncomputable abbrev canonicalOppositeUnipotentRadicalCompactOpen
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalOppositeUnipotentRadicalTopology B
    (U : Set (B.oppositeUnipotentRadical F.Carrier)) →
      U ∈ 𝓝 (1 : B.oppositeUnipotentRadical F.Carrier) →
        {L : OpenSubgroup (B.oppositeUnipotentRadical F.Carrier) //
          IsCompact (L : Set (B.oppositeUnipotentRadical F.Carrier)) ∧
            (L : Set (B.oppositeUnipotentRadical F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.oppositeUnipotentRadicalCompactOpen B

/-- Canonical nonarchimedean certificate for the actual product Levi. -/
noncomputable abbrev canonicalLeviNonarchimedean
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalLeviTopology B
    NonarchimedeanGroup (B.Levi F.Carrier) :=
  F.canonicalTopologicalData.leviNonarchimedean B

/-- Canonically realized compact open subgroups in every identity neighborhood of the product Levi. -/
noncomputable abbrev canonicalLeviCompactOpen
    (F : PadicField.{u} p) {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := F.canonicalLeviTopology B
    (U : Set (B.Levi F.Carrier)) → U ∈ 𝓝 (1 : B.Levi F.Carrier) →
      {L : OpenSubgroup (B.Levi F.Carrier) //
        IsCompact (L : Set (B.Levi F.Carrier)) ∧ (L : Set (B.Levi F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.leviCompactOpen B

/-- Canonical nonarchimedean certificate for the actual full upper unipotent subgroup. -/
noncomputable abbrev canonicalUpperUnipotentNonarchimedean
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalUpperUnipotentTopology n
    NonarchimedeanGroup (GeneralLinear.upperUnipotent n F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentNonarchimedean n

/-- Canonically realized compact open subgroups in every identity neighborhood of the full upper unipotent subgroup. -/
noncomputable abbrev canonicalUpperUnipotentCompactOpen
    (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalUpperUnipotentTopology n
    (U : Set (GeneralLinear.upperUnipotent n F.Carrier)) → U ∈ 𝓝 (1 : GeneralLinear.upperUnipotent n F.Carrier) →
      {L : OpenSubgroup (GeneralLinear.upperUnipotent n F.Carrier) //
        IsCompact (L : Set (GeneralLinear.upperUnipotent n F.Carrier)) ∧ (L : Set (GeneralLinear.upperUnipotent n F.Carrier)) ⊆ U} :=
  F.canonicalTopologicalData.upperUnipotentCompactOpen n

end Langlands.PadicField
