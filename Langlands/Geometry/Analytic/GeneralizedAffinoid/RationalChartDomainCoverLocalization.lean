import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainLocalization

/-! # Finite full-domain covers inside an actual rational chart -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- The rational spectrum embedding restricts to a homeomorphism from an
inner domain locus onto its actual extended locus. -/
def extendDomainLocusHomeomorph (d : RationalChart K A) (U : Domain K d.algebra) :
    U.locus ≃ₜ (d.extendDomain U).locus :=
  (d.spectrumMap.continuous.isClosedEmbedding d.spectrumMap_injective).isEmbedding.homeomorphImage
    U.locus

@[simp] theorem extendDomainLocusHomeomorph_apply_coe (d : RationalChart K A)
    (U : Domain K d.algebra) (x : U.locus) :
    (d.extendDomainLocusHomeomorph U x : BanachSpectrum A) = d.spectrumMap x := rfl

/-- The inverse-image locus of an ambient domain inside the chart is
homeomorphic to its original locus by the actual rational spectrum map. -/
def restrictDomainLocusHomeomorph (d : RationalChart K A) (V : Domain K A)
    (f : V ⟶ d.toDomain) : (d.restrictDomain V f).locus ≃ₜ V.locus :=
  (d.spectrumMap.continuous.isClosedEmbedding d.spectrumMap_injective).isEmbedding.homeomorphOfSubsetRange
    (by
      intro x hx
      rw [show Set.range d.spectrumMap = d.locus from d.represents.2.1]
      exact f.subset hx)

@[simp] theorem restrictDomainLocusHomeomorph_apply_coe (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) (x : (d.restrictDomain V f).locus) :
    (d.restrictDomainLocusHomeomorph V f x : BanachSpectrum A) =
      d.spectrumMap x := rfl

/-- Actual extension preserves and reflects pointwise covering by any
indexed family, using the proved rational spectrum injectivity. -/
theorem familyCovers_extendDomain_iff (d : RationalChart K A)
    (U : Domain K d.algebra) {ι : Type v} (obj : ι → Domain K d.algebra) :
    (∀ x ∈ (d.extendDomain U).locus, ∃ i, x ∈ (d.extendDomain (obj i)).locus) ↔
      (∀ x ∈ U.locus, ∃ i, x ∈ (obj i).locus) := by
  constructor
  · intro h x hx
    obtain ⟨i, y, hy, heq⟩ := h (d.spectrumMap x) ⟨x, hx, rfl⟩
    exact ⟨i, d.spectrumMap_injective heq ▸ hy⟩
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, hi⟩ := h y hy
    exact ⟨i, y, hi, rfl⟩

/-- Actual restriction preserves and reflects pointwise covering of an
ambient domain equipped with its inclusion into the rational chart. -/
theorem familyCovers_restrictDomain_iff (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) {ι : Type v}
    (obj : ι → Domain K A) (map : ∀ i, obj i ⟶ V) :
    (∀ x ∈ (d.restrictDomain V f).locus,
      ∃ i, x ∈ (d.restrictDomain (obj i) (map i ≫ f)).locus) ↔
      (∀ x ∈ V.locus, ∃ i, x ∈ (obj i).locus) := by
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := (d.restrictDomainLocusHomeomorph V f).surjective ⟨x, hx⟩
    have heq : d.spectrumMap y = x :=
      congrArg (fun z : V.locus => (z : BanachSpectrum A)) hy
    obtain ⟨i, hi⟩ := h y y.property
    exact ⟨i, heq ▸ hi⟩
  · intro h x hx
    exact h (d.spectrumMap x) hx

/-- Extend a finite cover to the original base, retaining the finite index,
every actual component algebra and every bounded target restriction. -/
def extendFiniteCover (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) : Domain.FiniteCover (d.extendDomain U) where
  size := c.size
  obj i := d.extendDomain (c.obj i)
  map i := d.extendDomainFunctor.map (c.map i)
  covers := (d.familyCovers_extendDomain_iff U c.obj).2 c.covers

@[simp] theorem extendFiniteCover_size (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (d.extendFiniteCover c).size = c.size := rfl

@[simp] theorem extendFiniteCover_obj (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    (d.extendFiniteCover c).obj i = d.extendDomain (c.obj i) := rfl

@[simp] theorem extendFiniteCover_obj_algebra (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((d.extendFiniteCover c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem extendFiniteCover_map_restriction (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((d.extendFiniteCover c).map i).restriction = (c.map i).restriction := rfl

@[simp] theorem extendFiniteCover_singleton (d : RationalChart K A)
    (U : Domain K d.algebra) :
    d.extendFiniteCover (Domain.FiniteCover.singleton U) =
      Domain.FiniteCover.singleton (d.extendDomain U) := rfl

/-- Restrict each actual component along its composite inclusion into the
chart. The original bounded target restrictions are retained literally. -/
def restrictFiniteCover (d : RationalChart K A) {V : Domain K A}
    (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) :
    Domain.FiniteCover (d.restrictDomain V f) where
  size := c.size
  obj i := d.restrictDomain (c.obj i) (c.map i ≫ f)
  map i := ⟨(c.map i).restriction, rfl⟩
  covers := (d.familyCovers_restrictDomain_iff V f c.obj c.map).2 c.covers

@[simp] theorem restrictFiniteCover_size (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) :
    (d.restrictFiniteCover f c).size = c.size := rfl

@[simp] theorem restrictFiniteCover_obj (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) (i : Fin c.size) :
    (d.restrictFiniteCover f c).obj i = d.restrictDomain (c.obj i) (c.map i ≫ f) := rfl

@[simp] theorem restrictFiniteCover_obj_algebra (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) (i : Fin c.size) :
    ((d.restrictFiniteCover f c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem restrictFiniteCover_map_restriction (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) (i : Fin c.size) :
    ((d.restrictFiniteCover f c).map i).restriction = (c.map i).restriction := rfl

@[simp] theorem restrictFiniteCover_singleton (d : RationalChart K A)
    (V : Domain K A) (f : V ⟶ d.toDomain) :
    d.restrictFiniteCover f (Domain.FiniteCover.singleton V) =
      Domain.FiniteCover.singleton (d.restrictDomain V f) := by
  rfl

/-- Extension's map from each unchanged component spectrum commutes with
the actual rational-spectrum homeomorphism of the target loci. -/
theorem extendFiniteCover_componentMap (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    (d.extendFiniteCover c).componentMap i =
      (d.extendDomainLocusHomeomorph U : C(U.locus, (d.extendDomain U).locus)).comp
        (c.componentMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Extension retains the actual disjoint union of component spectra, and
its finite spectrum-cover map commutes over the induced locus homeomorphism. -/
theorem extendFiniteCover_totalMap (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (d.extendFiniteCover c).totalMap =
      (d.extendDomainLocusHomeomorph U : C(U.locus, (d.extendDomain U).locus)).comp
        c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, (d.extendDomain U).locus) => g x.2)
    (d.extendFiniteCover_componentMap c x.1)

/-- Restriction's component spectrum triangle is the actual composite
inclusion equation, viewed over the original target locus. -/
theorem restrictFiniteCover_componentMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) (i : Fin c.size) :
    (d.restrictDomainLocusHomeomorph V f :
      C((d.restrictDomain V f).locus, V.locus)).comp
        ((d.restrictFiniteCover f c).componentMap i) = c.componentMap i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (c.map i ≫ f).spectrumMap_over_base x

/-- Restriction also retains the actual disjoint union of component spectra
and the finite spectrum-cover diagram over the induced locus homeomorphism. -/
theorem restrictFiniteCover_totalMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) :
    (d.restrictDomainLocusHomeomorph V f :
      C((d.restrictDomain V f).locus, V.locus)).comp
        (d.restrictFiniteCover f c).totalMap = c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, V.locus) => g x.2)
    (d.restrictFiniteCover_componentMap f c x.1)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
