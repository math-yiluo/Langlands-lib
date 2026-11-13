import Langlands.Group.GL.CompactOpen
import Langlands.AllField.Group.GL.PadicBlocks
import Langlands.AllField.Group.GL.PadicUpperUnipotent
/-!
# Compact open subgroups for actual local-field matrix groups
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

/-- The actual GL topology from any supplied local-field realization is nonarchimedean. -/
theorem generalLinearNonarchimedean (T : LocalFieldData F) (n : ℕ) :
    letI := T.generalLinearTopology n
    NonarchimedeanGroup (GeneralLinear n F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact Langlands.valuativeGeneralLinearNonarchimedean F n

/-- The actual product Levi is nonarchimedean in the supplied topology. -/
theorem leviNonarchimedean (T : LocalFieldData F) {n : ℕ}
    (B : GeneralLinear.BlockShape n) :
    letI := T.leviTopology B
    NonarchimedeanGroup (B.Levi F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearNonarchimedean n
  let := inducedNonarchimedean (B.leviSubgroup F).subtype .subtypeVal
  exact inducedNonarchimedean (B.leviEquivContinuous F).toMonoidHom
    (B.leviEquivContinuous F).toHomeomorph.isInducing

/-- The full upper unipotent subgroup is nonarchimedean in the supplied topology. -/
theorem upperUnipotentNonarchimedean (T : LocalFieldData F) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    NonarchimedeanGroup (GeneralLinear.upperUnipotent n F) := by
  let := T.topology
  let := T.generalLinearNonarchimedean n
  exact inducedNonarchimedean (GeneralLinear.upperUnipotent n F).subtype .subtypeVal

/-- Choose a compact open subgroup inside an upper-unipotent identity neighborhood. -/
noncomputable def upperUnipotentCompactOpen (T : LocalFieldData F) (n : ℕ) :
    letI := T.upperUnipotentTopology n
    (U : Set (GeneralLinear.upperUnipotent n F)) →
      U ∈ 𝓝 (1 : GeneralLinear.upperUnipotent n F) →
        {L : OpenSubgroup (GeneralLinear.upperUnipotent n F) //
          IsCompact (L : Set (GeneralLinear.upperUnipotent n F)) ∧
            (L : Set (GeneralLinear.upperUnipotent n F)) ⊆ U} := by
  letI := T.topology
  letI := T.upperUnipotentNonarchimedean n
  letI := T.upperUnipotentLocallyCompactSpace n
  exact chooseCompactOpen _

end LocalFieldData

end Langlands
