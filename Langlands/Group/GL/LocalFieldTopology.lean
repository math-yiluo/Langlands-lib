import Langlands.Group.GL.Nonarchimedean
import Langlands.Group.GL.UpperUnipotent
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Topological certificates over an arbitrary nonarchimedean local field

For a field `F` with `ValuativeRel F`, a topology and `IsNonarchimedeanLocalField F`
(any characteristic), these theorems supply the topological properties of `F`, its
units, the actual matrix group `GL_n(F)` and its upper unipotent subgroup that the
p-adic files obtain from `PadicField.TopologicalData`. They are explicit certificates,
not global instances.
-/

open Topology

namespace Langlands.LocalFieldTopology

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The rank-one structure of the valuation of a nonarchimedean local field. -/
@[instance_reducible]
private noncomputable def rankOne :
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    (Valued.v (R := F)).RankOne := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  exact
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }

/-- The field is Hausdorff. -/
theorem t2Space : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The field is second countable. -/
theorem secondCountableTopology : SecondCountableTopology F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let := rankOne F
  open scoped Valued in
    have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    infer_instance

/-- The field is totally disconnected. -/
theorem totallyDisconnectedSpace : TotallyDisconnectedSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  let := rankOne F
  open scoped Valued in
    infer_instance

/-- The unit group is locally compact. -/
theorem units_locallyCompactSpace : LocallyCompactSpace Fˣ := by
  have := t2Space F
  have hopen : IsOpen (Set.range (Units.val : Fˣ → F)) := by
    have : Set.range (Units.val : Fˣ → F) = {0}ᶜ := by
      ext x
      simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
    rw [this]
    exact isOpen_compl_singleton
  exact (IsOpenEmbedding.mk Units.isEmbedding_val₀ hopen).locallyCompactSpace

/-- The unit group is totally disconnected. -/
theorem units_totallyDisconnectedSpace : TotallyDisconnectedSpace Fˣ := by
  have := totallyDisconnectedSpace F
  exact Units.isEmbedding_val₀.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

variable (n : ℕ)

/-- `GL_n(F)` is Hausdorff. -/
theorem generalLinear_t2Space : T2Space (GeneralLinear n F) := by
  have := t2Space F
  infer_instance

/-- `GL_n(F)` is locally compact. -/
theorem generalLinear_locallyCompactSpace : LocallyCompactSpace (GeneralLinear n F) := by
  have := t2Space F
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → F))
  infer_instance

/-- `GL_n(F)` is second countable. -/
theorem generalLinear_secondCountableTopology :
    SecondCountableTopology (GeneralLinear n F) := by
  have := secondCountableTopology F
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → F))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- `GL_n(F)` is sigma compact. -/
theorem generalLinear_sigmaCompactSpace : SigmaCompactSpace (GeneralLinear n F) := by
  have := generalLinear_secondCountableTopology F n
  have := generalLinear_locallyCompactSpace F n
  infer_instance

/-- `GL_n(F)` is a nonarchimedean group. -/
theorem generalLinear_nonarchimedean : NonarchimedeanGroup (GeneralLinear n F) :=
  valuativeGeneralLinearNonarchimedean F n

/-- `GL_n(F)` is totally disconnected. -/
theorem generalLinear_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (GeneralLinear n F) := by
  have := totallyDisconnectedSpace F
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) F) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → F))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- Every identity neighborhood of `GL_n(F)` contains a compact open subgroup. -/
theorem generalLinear_compactOpen (U : Set (GeneralLinear n F))
    (hU : U ∈ 𝓝 (1 : GeneralLinear n F)) :
    ∃ L : OpenSubgroup (GeneralLinear n F), IsCompact (L : Set (GeneralLinear n F)) ∧
      (L : Set (GeneralLinear n F)) ⊆ U := by
  have := generalLinear_nonarchimedean F n
  have := generalLinear_locallyCompactSpace F n
  exact compactOpenSubgroupBasis _ U hU

/-- The upper unipotent subgroup is Hausdorff. -/
theorem upperUnipotent_t2Space : T2Space (GeneralLinear.upperUnipotent n F) := by
  have := generalLinear_t2Space F n
  infer_instance

/-- The upper unipotent subgroup is locally compact. -/
theorem upperUnipotent_locallyCompactSpace :
    LocallyCompactSpace (GeneralLinear.upperUnipotent n F) := by
  have := t2Space F
  have := generalLinear_locallyCompactSpace F n
  exact GeneralLinear.UpperUnipotent.locallyCompactSpace

/-- The upper unipotent subgroup is second countable. -/
theorem upperUnipotent_secondCountableTopology :
    SecondCountableTopology (GeneralLinear.upperUnipotent n F) := by
  have := generalLinear_secondCountableTopology F n
  exact IsEmbedding.subtypeVal.secondCountableTopology

/-- The upper unipotent subgroup is a nonarchimedean group. -/
theorem upperUnipotent_nonarchimedean :
    NonarchimedeanGroup (GeneralLinear.upperUnipotent n F) := by
  have := generalLinear_nonarchimedean F n
  exact
    { is_nonarchimedean := fun V hV => by
        rw [IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hV
        obtain ⟨W, hW, hWV⟩ := hV
        obtain ⟨L, hL⟩ := NonarchimedeanGroup.is_nonarchimedean W (by simpa using hW)
        exact ⟨OpenSubgroup.comap (GeneralLinear.upperUnipotent n F).subtype
          continuous_subtype_val L, fun x hx => hWV (hL hx)⟩ }

end Langlands.LocalFieldTopology
