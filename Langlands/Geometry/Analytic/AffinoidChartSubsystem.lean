import Langlands.Geometry.Analytic.AffinoidChartGluing
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties

/-! # Open subsystems of affinoid chart gluings -/

noncomputable section

universe u w

namespace Langlands.Analytic.AffinoidChartSystem

open Set Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (C : AffinoidChartSystem.{u, w} K)

/-- A family of charts containing every subdomain of any of its members. -/
def IsDownwardClosed (S : Set C.Index) : Prop :=
  ∀ {i j : C.Index}, C.Sub i j → j ∈ S → i ∈ S

/-- Restrict a chart system to a downward closed family. The chart algebras
and bounded restrictions are the original ones. -/
def subsystem (S : Set C.Index) (hS : C.IsDownwardClosed S) :
    AffinoidChartSystem.{u, w} K where
  Index := S
  algebra i := C.algebra i.val
  Sub i j := C.Sub i.val j.val
  restriction i j h := C.restriction i.val j.val h
  sub_refl i := C.sub_refl i.val
  sub_trans := C.sub_trans
  restriction_refl i := C.restriction_refl i.val
  restriction_trans := C.restriction_trans
  represents i j h := C.represents i.val j.val h
  meet := by
    intro i j k hik hjk t hti htj
    obtain ⟨l, hli, hlj, ht⟩ := C.meet hik hjk t hti htj
    exact ⟨⟨l, hS hli i.property⟩, hli, hlj, ht⟩

/-- The natural map from the subsystem quotient to the full gluing. -/
def subsystemMap (S : Set C.Index) (hS : C.IsDownwardClosed S) :
    (C.subsystem S hS).Space → C.Space :=
  Quotient.lift (fun a => C.chart a.1.val a.2) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ ⟨k, hki, hkj, v, hvs, hvt⟩
    exact C.chart_eq_iff.mpr ⟨k.val, hki, hkj, v, hvs, hvt⟩)

@[simp]
theorem subsystemMap_chart (S : Set C.Index) (hS : C.IsDownwardClosed S)
    (i : S) (s : BanachSpectrum (C.algebra i.val)) :
    C.subsystemMap S hS ((C.subsystem S hS).chart i s) = C.chart i.val s := rfl

/-- Downward closure ensures that the full gluing makes no additional
identifications between subsystem points. -/
theorem subsystemMap_injective (S : Set C.Index) (hS : C.IsDownwardClosed S) :
    Function.Injective (C.subsystemMap S hS) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      intro h
      obtain ⟨k, hka, hkb, t, hta, htb⟩ := C.chart_eq_iff.mp h
      exact (C.subsystem S hS).chart_eq_iff.mpr
        ⟨⟨k, hS hka a.1.property⟩, hka, hkb, t, hta, htb⟩

theorem continuous_subsystemMap (S : Set C.Index) (hS : C.IsDownwardClosed S) :
    Continuous (C.subsystemMap S hS) := by
  apply Continuous.quotient_lift
  exact continuous_sigma fun i => C.continuous_chart i.val

/-- The union of the original chart images selected by the subsystem. -/
def subsystemSupport (S : Set C.Index) : Set C.Space :=
  {z | ∃ i : S, z ∈ Set.range (C.chart i.val)}

theorem range_subsystemMap (S : Set C.Index) (hS : C.IsDownwardClosed S) :
    Set.range (C.subsystemMap S hS) = C.subsystemSupport S := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, s, rfl⟩ := (C.subsystem S hS).exists_chart x
    exact ⟨i, s, rfl⟩
  · rintro ⟨i, s, rfl⟩
    exact ⟨(C.subsystem S hS).chart i s, rfl⟩

/-- A contained subsystem chart, in the actual open-patch preimage inside
an original chart spectrum. -/
def relativePull (S : Set C.Index) (i : S) (j : C.Index) (h : C.Sub i.val j) :
    BanachSpectrum (C.algebra i.val) → (C.chart j ⁻¹' C.subsystemSupport S) :=
  fun t => ⟨C.pull h t, i, t, (C.chart_pull h t).symm⟩

theorem isEmbedding_relativePull (S : Set C.Index) (i : S) (j : C.Index)
    (h : C.Sub i.val j) : IsEmbedding (C.relativePull S i j h) :=
  (PresentedAffinoidAlgebra.Domain.spectrumEmbedding K (C.algebra j)
    (C.toDomain h)).isEmbedding.codRestrict
      (C.chart j ⁻¹' C.subsystemSupport S) (fun t => ⟨i, t, (C.chart_pull h t).symm⟩)

/-- The images of all subsystem subcharts of one original chart, viewed
inside the preimage of the subsystem support. -/
def relativePullFamily (S : Set C.Index) (j : C.Index) :
    Set (Set (C.chart j ⁻¹' C.subsystemSupport S)) :=
  {F | ∃ (i : S) (h : C.Sub i.val j), F = Set.range (C.relativePull S i j h)}

/-- Contained subsystem charts give finite relative neighborhoods on every
original chart over the support. -/
def HasLocalSubchartCover (S : Set C.Index) : Prop :=
  ∀ j : C.Index, AtlasTopology.IsQuasinet (C.relativePullFamily S j)

/-- Openness of a subsystem support can be checked in the original spectra. -/
theorem isOpen_subsystemSupport (S : Set C.Index)
    (hOpen : ∀ j : C.Index, IsOpen (C.chart j ⁻¹' C.subsystemSupport S)) :
    IsOpen (C.subsystemSupport S) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_sigma_iff]
  exact hOpen

/-- If the support is chartwise open and contained subsystem charts give
quasinets in all chart preimages, its gluing is an actual open subspace of
the full quotient. No Hausdorff or global finite-overlap hypothesis is used. -/
theorem isOpenEmbedding_subsystemMap (S : Set C.Index) (hS : C.IsDownwardClosed S)
    (hOpen : ∀ j : C.Index, IsOpen (C.chart j ⁻¹' C.subsystemSupport S))
    (hCover : C.HasLocalSubchartCover S) :
    IsOpenEmbedding (C.subsystemMap S hS) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (C.continuous_subsystemMap S hS) (C.subsystemMap_injective S hS) ?_
  intro V hV
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage, isOpen_sigma_iff]
  intro j
  let U := C.chart j ⁻¹' C.subsystemSupport S
  let W : Set U := Subtype.val ⁻¹' (C.chart j ⁻¹' (C.subsystemMap S hS '' V))
  have hW : IsOpen W := by
    apply ((hCover j).isOpen_iff W).mpr
    rintro F ⟨i, h, rfl⟩
    let e := (C.isEmbedding_relativePull S i j h).toHomeomorph
    apply e.isQuotientMap.isOpen_preimage.mp
    have heq : e ⁻¹' (Subtype.val ⁻¹' W) = (C.subsystem S hS).chart i ⁻¹' V := by
      ext t
      change (C.chart j (C.pull h t) ∈ C.subsystemMap S hS '' V) ↔ _
      rw [C.chart_pull]
      constructor
      · rintro ⟨x, hx, hxt⟩
        have he : x = (C.subsystem S hS).chart i t :=
          C.subsystemMap_injective S hS hxt
        change (C.subsystem S hS).chart i t ∈ V
        simpa only [he] using hx
      · intro ht
        exact ⟨(C.subsystem S hS).chart i t, ht, rfl⟩
    rw [heq]
    exact hV.preimage ((C.subsystem S hS).continuous_chart i)
  have hopen : IsOpen (Subtype.val '' W : Set (BanachSpectrum (C.algebra j))) :=
    (hOpen j).isOpenEmbedding_subtypeVal.isOpenMap W hW
  have heq : (Subtype.val '' W : Set (BanachSpectrum (C.algebra j))) =
      C.chart j ⁻¹' (C.subsystemMap S hS '' V) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ht
      have hs : C.chart j t ∈ C.subsystemSupport S := by
        rw [← C.range_subsystemMap S hS]
        obtain ⟨x, -, hxt⟩ := ht
        exact ⟨x, hxt⟩
      exact ⟨⟨t, hs⟩, ht, rfl⟩
  rwa [heq] at hopen

end Langlands.Analytic.AffinoidChartSystem
