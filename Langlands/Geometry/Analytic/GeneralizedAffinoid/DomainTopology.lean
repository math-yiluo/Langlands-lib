import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain
import Langlands.Geometry.Analytic.Spectrum.Properties

/-! # Compact domain loci and descent for finite actual domain covers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {A : PresentedAffinoidAlgebra K}

/-- A full domain locus is compact in its actual base spectrum. -/
theorem isCompact_locus (U : Domain K A) : IsCompact U.locus :=
  U.represents.1.isCompact

instance compactSpace_locus (U : Domain K A) : CompactSpace U.locus :=
  (isCompact_iff_compactSpace).mp U.isCompact_locus

/-- The actual representing spectrum maps closed sets to closed sets in the locus. -/
theorem spectrumToLocus_isClosedMap (U : Domain K A) : IsClosedMap U.spectrumToLocus :=
  U.spectrumToLocus.continuous.isClosedMap

/-- The structural surjection determines the locus topology, without an injectivity claim. -/
theorem spectrumToLocus_isQuotientMap (U : Domain K A) :
    IsQuotientMap U.spectrumToLocus :=
  .of_surjective_continuous U.spectrumToLocus_surjective U.spectrumToLocus.continuous

theorem isOpen_iff_spectrumToLocus (U : Domain K A) (s : Set U.locus) :
    IsOpen s ↔ IsOpen (U.spectrumToLocus ⁻¹' s) :=
  U.spectrumToLocus_isQuotientMap.isCoinducing.isOpen_preimage.symm

theorem isClosed_iff_spectrumToLocus (U : Domain K A) (s : Set U.locus) :
    IsClosed s ↔ IsClosed (U.spectrumToLocus ⁻¹' s) :=
  U.spectrumToLocus_isQuotientMap.isCoinducing.isClosed_preimage.symm

theorem continuous_iff_spectrumToLocus (U : Domain K A)
    {Y : Type v} [TopologicalSpace Y] (g : U.locus → Y) :
    Continuous g ↔ Continuous (g ∘ U.spectrumToLocus) :=
  U.spectrumToLocus_isQuotientMap.continuous_iff

/-- Actual domain restrictions induce closed embeddings of the represented loci. -/
theorem Inclusion.locusMap_isClosedEmbedding {U V : Domain K A} (f : U ⟶ V) :
    IsClosedEmbedding f.locusMap :=
  f.locusMap.continuous.isClosedEmbedding fun _ _ h =>
    Subtype.ext (congrArg (fun z : V.locus => (z : BanachSpectrum A)) h)

/-- A finite cover stores full domain representations, actual bounded restrictions
to its target, and pointwise covering of the target locus. -/
structure FiniteCover (V : Domain K A) where
  size : ℕ
  obj : Fin size → Domain K A
  map : ∀ i, obj i ⟶ V
  covers : ∀ x ∈ V.locus, ∃ i, x ∈ (obj i).locus

namespace FiniteCover

variable {V : Domain K A}

/-- The identity restriction gives a concrete singleton cover. -/
def singleton (V : Domain K A) : FiniteCover V where
  size := 1
  obj _ := V
  map _ := 𝟙 V
  covers _ hx := ⟨0, hx⟩

/-- An empty target locus admits the empty family, including for zero quotients. -/
def empty (V : Domain K A) (hV : V.locus = ∅) : FiniteCover V where
  size := 0
  obj i := Fin.elim0 i
  map i := Fin.elim0 i
  covers x hx := by simp [hV] at hx

theorem locus_eq_empty_of_size_eq_zero (c : FiniteCover V) (h : c.size = 0) :
    V.locus = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨i, _⟩ := c.covers x hx
  have hi := i.isLt
  simp [h] at hi

/-- The component spectrum maps to the target through its represented locus.
The intervening domain arrow retains its actual bounded restriction. -/
def componentMap (c : FiniteCover V) (i : Fin c.size) :
    C(BanachSpectrum (c.obj i).algebra, V.locus) :=
  (c.map i).locusMap.comp (c.obj i).spectrumToLocus

theorem componentMap_isClosedMap (c : FiniteCover V) (i : Fin c.size) :
    IsClosedMap (c.componentMap i) :=
  (c.componentMap i).continuous.isClosedMap

/-- The map from the disjoint union of the actual representing spectra. -/
def totalMap (c : FiniteCover V) :
    C((Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra), V.locus) where
  toFun x := c.componentMap x.1 x.2
  continuous_toFun := continuous_sigma fun i => (c.componentMap i).continuous

@[simp] theorem totalMap_mk (c : FiniteCover V) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    c.totalMap ⟨i, x⟩ = c.componentMap i x := rfl

/-- Covering of loci and the exact structural spectrum images give surjectivity. -/
theorem totalMap_surjective (c : FiniteCover V) : Function.Surjective c.totalMap := by
  intro x
  obtain ⟨i, hi⟩ := c.covers x.val x.property
  obtain ⟨y, hy⟩ := (c.obj i).spectrumToLocus_surjective ⟨x.val, hi⟩
  refine ⟨⟨i, y⟩, ?_⟩
  exact Subtype.ext
    (congrArg (fun z : (c.obj i).locus => (z : BanachSpectrum A)) hy)

/-- Finiteness makes the disjoint union compact, so this map is closed. -/
theorem totalMap_isClosedMap (c : FiniteCover V) : IsClosedMap c.totalMap :=
  c.totalMap.continuous.isClosedMap

/-- The finite actual spectrum cover presents the target's subspace topology. -/
theorem totalMap_isQuotientMap (c : FiniteCover V) : IsQuotientMap c.totalMap :=
  .of_surjective_continuous c.totalMap_surjective c.totalMap.continuous

/-- Openness is detected on every actual representing spectrum in the cover. -/
theorem isOpen_iff (c : FiniteCover V) (s : Set V.locus) :
    IsOpen s ↔ ∀ i, IsOpen (c.componentMap i ⁻¹' s) := by
  rw [← c.totalMap_isQuotientMap.isCoinducing.isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- Closedness is detected on every actual representing spectrum in the cover. -/
theorem isClosed_iff (c : FiniteCover V) (s : Set V.locus) :
    IsClosed s ↔ ∀ i, IsClosed (c.componentMap i ⁻¹' s) := by
  rw [← c.totalMap_isQuotientMap.isCoinducing.isClosed_preimage, isClosed_sigma_iff]
  rfl

/-- Continuity into any topological target is detected on all component spectra. -/
theorem continuous_iff (c : FiniteCover V) {Y : Type v} [TopologicalSpace Y]
    (g : V.locus → Y) :
    Continuous g ↔ ∀ i, Continuous (g ∘ c.componentMap i) :=
  c.totalMap_isQuotientMap.continuous_iff.trans continuous_sigma_iff

/-- Equivalent openness detection directly on the component domain loci. -/
theorem isOpen_iff_loci (c : FiniteCover V) (s : Set V.locus) :
    IsOpen s ↔ ∀ i, IsOpen ((c.map i).locusMap ⁻¹' s) := by
  rw [c.isOpen_iff]
  exact forall_congr' fun i =>
    ((c.obj i).isOpen_iff_spectrumToLocus ((c.map i).locusMap ⁻¹' s)).symm

/-- Equivalent closedness detection directly on the component domain loci. -/
theorem isClosed_iff_loci (c : FiniteCover V) (s : Set V.locus) :
    IsClosed s ↔ ∀ i, IsClosed ((c.map i).locusMap ⁻¹' s) := by
  rw [c.isClosed_iff]
  exact forall_congr' fun i =>
    ((c.obj i).isClosed_iff_spectrumToLocus ((c.map i).locusMap ⁻¹' s)).symm

/-- Equivalent continuity detection directly on the component domain loci. -/
theorem continuous_iff_loci (c : FiniteCover V) {Y : Type v} [TopologicalSpace Y]
    (g : V.locus → Y) :
    Continuous g ↔ ∀ i, Continuous (g ∘ (c.map i).locusMap) := by
  rw [c.continuous_iff]
  exact forall_congr' fun i =>
    ((c.obj i).continuous_iff_spectrumToLocus (g ∘ (c.map i).locusMap)).symm

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
