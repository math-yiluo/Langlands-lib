import Langlands.AllFieldBZ.Group.GL.PadicBlocks
import Langlands.Group.GL.CompactOpen

/-!
# All-field port of `Langlands.Group.GL.CompactOpen`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.CompactOpen` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open Filter
open Topology
namespace Langlands.AllFieldBZ.LocalFieldPackage
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

variable {F : LocalFieldPackage.{u}}

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

end TopologicalData
end Langlands.AllFieldBZ.LocalFieldPackage
