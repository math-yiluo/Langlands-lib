import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEmbeddedLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Finite full-domain covers along a specified embedded domain -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- The relative locus of a contained ambient domain is homeomorphic to its
original locus through the specified injective structural spectrum map. -/
def relativeLocusHomeomorphOfInjective (d : Domain K A)
    (hd : Function.Injective d.spectrumMap) (V : Domain K A)
    (f : V ⟶ d) : (d.relative V f).locus ≃ₜ V.locus :=
  (Homeomorph.setCongr (d.relative_locus_eq_preimage_of_injective hd V f)).trans
    ((d.spectrumMap.continuous.isClosedEmbedding hd).isEmbedding.homeomorphOfSubsetRange
      (by
        intro x hx
        rw [show Set.range d.spectrumMap = d.locus from d.represents.2.1]
        exact f.subset hx))

@[simp] theorem relativeLocusHomeomorphOfInjective_apply_coe (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    (V : Domain K A) (f : V ⟶ d) (x : (d.relative V f).locus) :
    (d.relativeLocusHomeomorphOfInjective hd V f x : BanachSpectrum A) =
      d.spectrumMap x := rfl

/-- Actual extension preserves and reflects pointwise covering by any
indexed family, using injectivity of the specified spectrum map. -/
theorem familyCovers_extendOfInjective_iff (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    (U : Domain K d.algebra) {ι : Type v} (obj : ι → Domain K d.algebra) :
    (∀ x ∈ (d.extendOfInjective hd U).locus, ∃ i, x ∈ (d.extendOfInjective hd (obj i)).locus) ↔
      (∀ x ∈ U.locus, ∃ i, x ∈ (obj i).locus) := by
  constructor
  · intro h x hx
    obtain ⟨i, y, hy, heq⟩ := h (d.spectrumMap x) ⟨x, hx, rfl⟩
    exact ⟨i, hd heq ▸ hy⟩
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, hi⟩ := h y hy
    exact ⟨i, y, hi, rfl⟩

/-- Actual restriction preserves and reflects pointwise covering of an
ambient domain equipped with its inclusion into the containing domain. -/
theorem familyCovers_relativeOfInjective_iff (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    (V : Domain K A) (f : V ⟶ d) {ι : Type v}
    (obj : ι → Domain K A) (map : ∀ i, obj i ⟶ V) :
    (∀ x ∈ (d.relative V f).locus,
      ∃ i, x ∈ (d.relative (obj i) (map i ≫ f)).locus) ↔
      (∀ x ∈ V.locus, ∃ i, x ∈ (obj i).locus) := by
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := (d.relativeLocusHomeomorphOfInjective hd V f).surjective ⟨x, hx⟩
    have heq : d.spectrumMap y = x :=
      congrArg (fun z : V.locus => (z : BanachSpectrum A)) hy
    obtain ⟨i, hi⟩ := h y y.property
    exact ⟨i, heq ▸ (d.relative_locus_subset_preimage (obj i) (map i ≫ f) hi)⟩
  · intro h x hx
    obtain ⟨i, hi⟩ := h (d.spectrumMap x) (d.relative_locus_subset_preimage V f hx)
    refine ⟨i, ?_⟩
    rw [d.relative_locus_eq_preimage_of_injective hd (obj i) (map i ≫ f)]
    exact hi

/-- Extend a finite cover to the original base, retaining the finite index,
every actual component algebra and every bounded target restriction. -/
def extendFiniteCoverOfInjective (d : Domain K A) (hd : Function.Injective d.spectrumMap) {U : Domain K d.algebra}
    (c : FiniteCover U) : FiniteCover (d.extendOfInjective hd U) where
  size := c.size
  obj i := d.extendOfInjective hd (c.obj i)
  map i := (d.extendOfInjectiveFunctor hd).map (c.map i)
  covers := (d.familyCovers_extendOfInjective_iff hd U c.obj).2 c.covers

@[simp] theorem extendFiniteCoverOfInjective_size (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) :
    (d.extendFiniteCoverOfInjective hd c).size = c.size := rfl

@[simp] theorem extendFiniteCoverOfInjective_obj (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) (i : Fin c.size) :
    (d.extendFiniteCoverOfInjective hd c).obj i = d.extendOfInjective hd (c.obj i) := rfl

@[simp] theorem extendFiniteCoverOfInjective_obj_algebra (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) (i : Fin c.size) :
    ((d.extendFiniteCoverOfInjective hd c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem extendFiniteCoverOfInjective_map_restriction (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) (i : Fin c.size) :
    ((d.extendFiniteCoverOfInjective hd c).map i).restriction = (c.map i).restriction := rfl

@[simp] theorem extendFiniteCoverOfInjective_singleton (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    (U : Domain K d.algebra) :
    d.extendFiniteCoverOfInjective hd (FiniteCover.singleton U) =
      FiniteCover.singleton (d.extendOfInjective hd U) := rfl

/-- Restrict each actual component along its composite inclusion into the
containing domain. Retain the original bounded target restrictions. -/
def relativeFiniteCoverOfInjective (d : Domain K A) (hd : Function.Injective d.spectrumMap) {V : Domain K A}
    (f : V ⟶ d) (c : FiniteCover V) :
    FiniteCover (d.relative V f) where
  size := c.size
  obj i := d.relative (c.obj i) (c.map i ≫ f)
  map i := ⟨(c.map i).restriction, rfl⟩
  covers := (d.familyCovers_relativeOfInjective_iff hd V f c.obj c.map).2 c.covers

@[simp] theorem relativeFiniteCoverOfInjective_size (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) :
    (d.relativeFiniteCoverOfInjective hd f c).size = c.size := rfl

@[simp] theorem relativeFiniteCoverOfInjective_obj (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) (i : Fin c.size) :
    (d.relativeFiniteCoverOfInjective hd f c).obj i = d.relative (c.obj i) (c.map i ≫ f) := rfl

@[simp] theorem relativeFiniteCoverOfInjective_obj_algebra (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) (i : Fin c.size) :
    ((d.relativeFiniteCoverOfInjective hd f c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem relativeFiniteCoverOfInjective_map_restriction (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) (i : Fin c.size) :
    ((d.relativeFiniteCoverOfInjective hd f c).map i).restriction = (c.map i).restriction := rfl

@[simp] theorem relativeFiniteCoverOfInjective_singleton (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    (V : Domain K A) (f : V ⟶ d) :
    d.relativeFiniteCoverOfInjective hd f (FiniteCover.singleton V) =
      FiniteCover.singleton (d.relative V f) := by
  rfl

/-- Extension's map from each unchanged component spectrum commutes with
the actual specified-spectrum homeomorphism of the target loci. -/
theorem extendFiniteCoverOfInjective_componentMap (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) (i : Fin c.size) :
    (d.extendFiniteCoverOfInjective hd c).componentMap i =
      (d.extendOfInjectiveLocusHomeomorph hd U : C(U.locus, (d.extendOfInjective hd U).locus)).comp
        (c.componentMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Extension retains the actual disjoint union of component spectra, and
its finite spectrum-cover map commutes over the induced locus homeomorphism. -/
theorem extendFiniteCoverOfInjective_totalMap (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {U : Domain K d.algebra} (c : FiniteCover U) :
    (d.extendFiniteCoverOfInjective hd c).totalMap =
      (d.extendOfInjectiveLocusHomeomorph hd U : C(U.locus, (d.extendOfInjective hd U).locus)).comp
        c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, (d.extendOfInjective hd U).locus) => g x.2)
    (d.extendFiniteCoverOfInjective_componentMap hd c x.1)

/-- Restriction's component spectrum triangle is the actual composite
inclusion equation, viewed over the original target locus. -/
theorem relativeFiniteCoverOfInjective_componentMap (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) (i : Fin c.size) :
    (d.relativeLocusHomeomorphOfInjective hd V f :
      C((d.relative V f).locus, V.locus)).comp
        ((d.relativeFiniteCoverOfInjective hd f c).componentMap i) = c.componentMap i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (c.map i ≫ f).spectrumMap_over_base x

/-- Restriction also retains the actual disjoint union of component spectra
and the finite spectrum-cover diagram over the induced locus homeomorphism. -/
theorem relativeFiniteCoverOfInjective_totalMap (d : Domain K A) (hd : Function.Injective d.spectrumMap)
    {V : Domain K A} (f : V ⟶ d) (c : FiniteCover V) :
    (d.relativeLocusHomeomorphOfInjective hd V f :
      C((d.relative V f).locus, V.locus)).comp
        (d.relativeFiniteCoverOfInjective hd f c).totalMap = c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, V.locus) => g x.2)
    (d.relativeFiniteCoverOfInjective_componentMap hd f c x.1)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
