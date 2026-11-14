import Langlands.Group.GL.CompactOpen
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.Group.GL.PadicOppositeBlocks
/-!
# Compact open subgroups for actual p-adic matrix groups
-/

open Filter Topology

namespace Langlands

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

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

/-- The actual upper block parabolic is nonarchimedean in the supplied topology. -/
theorem parabolicNonarchimedean (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    NonarchimedeanGroup (B.parabolic F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  exact inducedNonarchimedean (B.parabolic F).subtype .subtypeVal

/-- The actual block unipotent radical is nonarchimedean in the supplied topology. -/
theorem unipotentRadicalNonarchimedean (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    NonarchimedeanGroup (B.unipotentRadical F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  let := T.parabolicNonarchimedean B
  exact inducedNonarchimedean (B.unipotentRadical F).subtype .subtypeVal

/-- Choose an actual compact open subgroup inside a GL identity neighborhood. -/
noncomputable def generalLinearCompactOpen (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    (U : Set (GeneralLinear n F)) → U ∈ 𝓝 (1 : GeneralLinear n F) →
      {L : OpenSubgroup (GeneralLinear n F) //
        IsCompact (L : Set (GeneralLinear n F)) ∧
          (L : Set (GeneralLinear n F)) ⊆ U} := by
  letI := T.topology
  letI := T.generalLinearNonarchimedean n
  letI := T.generalLinearLocallyCompactSpace n
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the upper block parabolic. -/
noncomputable def parabolicCompactOpen (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.parabolicTopology B
    (U : Set (B.parabolic F)) → U ∈ 𝓝 (1 : B.parabolic F) →
      {L : OpenSubgroup (B.parabolic F) //
        IsCompact (L : Set (B.parabolic F)) ∧ (L : Set (B.parabolic F)) ⊆ U} := by
  letI := T.topology
  letI := T.parabolicNonarchimedean B
  letI := T.parabolicLocallyCompactSpace B
  exact chooseCompactOpen _

/-- Choose a compact open subgroup inside an identity neighborhood of the block unipotent radical. -/
noncomputable def unipotentRadicalCompactOpen (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.unipotentRadicalTopology B
    (U : Set (B.unipotentRadical F)) → U ∈ 𝓝 (1 : B.unipotentRadical F) →
      {L : OpenSubgroup (B.unipotentRadical F) //
        IsCompact (L : Set (B.unipotentRadical F)) ∧ (L : Set (B.unipotentRadical F)) ⊆ U} := by
  letI := T.topology
  letI := T.unipotentRadicalNonarchimedean B
  letI := T.unipotentRadicalLocallyCompactSpace B
  exact chooseCompactOpen _

end LocalFieldData

end Langlands
