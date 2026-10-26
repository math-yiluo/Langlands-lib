import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Langlands.Topology.CompactOpen.NeighborhoodBasis

open Set Filter TopologicalSpace Topology

universe u

namespace Langlands.Topology

/-- Every neighborhood contains a compact open neighborhood of its base point. -/
def HasCompactOpenNeighborhoodBasis (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
    ∃ V : Set X, x ∈ V ∧ IsOpen V ∧ IsCompact V ∧ V ⊆ U

/-- Renard II.1.1's t.d. spaces: Hausdorff spaces with a compact open neighborhood basis. -/
def IsLocallyProfinite (X : Type u) [TopologicalSpace X] : Prop :=
  T2Space X ∧ HasCompactOpenNeighborhoodBasis X

variable {X : Type u} [TopologicalSpace X]

theorem HasCompactOpenNeighborhoodBasis.mem_nhds_iff
    (h : HasCompactOpenNeighborhoodBasis X) {x : X} {U : Set X} :
    U ∈ 𝓝 x ↔ ∃ V : Set X, x ∈ V ∧ IsOpen V ∧ IsCompact V ∧ V ⊆ U :=
  ⟨h x U, fun ⟨_, hxV, ho, _, hVU⟩ => mem_of_superset (ho.mem_nhds hxV) hVU⟩

theorem HasCompactOpenNeighborhoodBasis.nhds_hasBasis
    (h : HasCompactOpenNeighborhoodBasis X) (x : X) :
    (𝓝 x).HasBasis (fun V : Set X => x ∈ V ∧ IsOpen V ∧ IsCompact V) id := by
  constructor
  intro U
  simpa only [and_assoc, id_eq] using h.mem_nhds_iff (x := x) (U := U)

theorem HasCompactOpenNeighborhoodBasis.isTopologicalBasis
    (h : HasCompactOpenNeighborhoodBasis X) :
    IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact V} := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ hV => hV.1)
  intro x U hxU hU
  obtain ⟨V, hxV, hVo, hVc, hVU⟩ := h x U (hU.mem_nhds hxU)
  exact ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩

theorem hasCompactOpenNeighborhoodBasis_iff_isTopologicalBasis :
    HasCompactOpenNeighborhoodBasis X ↔
      IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact V} := by
  refine ⟨HasCompactOpenNeighborhoodBasis.isTopologicalBasis, ?_⟩
  intro h x U hU
  obtain ⟨V, ⟨hVo, hVc⟩, hxV, hVU⟩ := h.mem_nhds_iff.mp hU
  exact ⟨V, hxV, hVo, hVc, hVU⟩

theorem isLocallyProfinite_iff_isTopologicalBasis :
    IsLocallyProfinite X ↔
      T2Space X ∧ IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact V} := by
  exact and_congr_right fun _ => hasCompactOpenNeighborhoodBasis_iff_isTopologicalBasis

theorem HasCompactOpenNeighborhoodBasis.locallyCompactSpace
    (h : HasCompactOpenNeighborhoodBasis X) : LocallyCompactSpace X where
  local_compact_nhds x U hU := by
    obtain ⟨V, hxV, hVo, hVc, hVU⟩ := h x U hU
    exact ⟨V, hVo.mem_nhds hxV, hVU, hVc⟩

theorem IsLocallyProfinite.t2Space (h : IsLocallyProfinite X) : T2Space X :=
  h.1

theorem IsLocallyProfinite.hasCompactOpenNeighborhoodBasis (h : IsLocallyProfinite X) :
    HasCompactOpenNeighborhoodBasis X :=
  h.2

theorem IsLocallyProfinite.locallyCompactSpace (h : IsLocallyProfinite X) :
    LocallyCompactSpace X :=
  h.2.locallyCompactSpace

theorem IsLocallyProfinite.totallyDisconnectedSpace (h : IsLocallyProfinite X) :
    TotallyDisconnectedSpace X := by
  let : T2Space X := h.t2Space
  have hb : IsTopologicalBasis {V : Set X | IsClopen V} :=
    h.2.isTopologicalBasis.of_isOpen_of_subset (fun _ hV => hV.isOpen)
      (fun _ hV => ⟨hV.2.isClosed, hV.1⟩)
  let : TotallySeparatedSpace X := totallySeparatedSpace_of_t0_of_basis_clopen hb
  infer_instance

/-- The reverse conversion uses Mathlib's locally compact clopen-basis theorem. -/
theorem hasCompactOpenNeighborhoodBasis_of_mathlib [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] : HasCompactOpenNeighborhoodBasis X := by
  intro x U hU
  obtain ⟨C, hCn, hCU, hCc⟩ := local_compact_nhds hU
  obtain ⟨V, hV, hxV, hVC⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp hCn
  exact ⟨V, hxV, hV.isOpen, hCc.of_isClosed_subset hV.isClosed hVC, hVC.trans hCU⟩

theorem isLocallyProfinite_of_mathlib [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] : IsLocallyProfinite X :=
  ⟨inferInstance, hasCompactOpenNeighborhoodBasis_of_mathlib⟩

theorem isLocallyProfinite_iff_mathlib :
    IsLocallyProfinite X ↔
      T2Space X ∧ LocallyCompactSpace X ∧ TotallyDisconnectedSpace X := by
  refine ⟨fun h => ⟨h.t2Space, h.locallyCompactSpace, h.totallyDisconnectedSpace⟩, ?_⟩
  rintro ⟨ht, hl, hd⟩
  let : T2Space X := ht
  let : LocallyCompactSpace X := hl
  let : TotallyDisconnectedSpace X := hd
  exact isLocallyProfinite_of_mathlib

/-- Hausdorffness supplies the R₁ hypothesis in Mathlib's weak-to-local conversion. -/
theorem isLocallyProfinite_of_weaklyLocallyCompactSpace [T2Space X]
    [WeaklyLocallyCompactSpace X] [TotallyDisconnectedSpace X] : IsLocallyProfinite X := by
  let : LocallyCompactSpace X := WeaklyLocallyCompactSpace.locallyCompactSpace
  exact isLocallyProfinite_of_mathlib

theorem isLocallyProfinite_iff_weaklyLocallyCompactSpace :
    IsLocallyProfinite X ↔
      T2Space X ∧ WeaklyLocallyCompactSpace X ∧ TotallyDisconnectedSpace X := by
  constructor
  · intro h
    let : LocallyCompactSpace X := h.locallyCompactSpace
    exact ⟨h.t2Space, inferInstance, h.totallyDisconnectedSpace⟩
  · rintro ⟨ht, hl, hd⟩
    let : T2Space X := ht
    let : WeaklyLocallyCompactSpace X := hl
    let : TotallyDisconnectedSpace X := hd
    exact isLocallyProfinite_of_weaklyLocallyCompactSpace

section Groups

variable {G : Type u} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

/-- Nonarchimedean groups need an explicit separation hypothesis for the source definition. -/
theorem isLocallyProfinite_of_nonarchimedean [T2Space G] [WeaklyLocallyCompactSpace G] :
    IsLocallyProfinite G :=
  isLocallyProfinite_of_weaklyLocallyCompactSpace

/-- The existing Library basis theorem applies after the source predicate supplies local
compactness. The nonarchimedean assumption remains explicit; no Van Dantzig theorem is used. -/
theorem IsLocallyProfinite.compactOpenSubgroupBasis (h : IsLocallyProfinite G) :
    ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G,
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := by
  let : LocallyCompactSpace G := h.locallyCompactSpace
  exact Langlands.compactOpenSubgroupBasis G

end Groups

end Langlands.Topology
