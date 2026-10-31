import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainNaturality
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverRefinement

/-! # Finite full-domain covers through nested actual rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {d e : RationalChart K A}

/-- Nested transport preserves and reflects covering by any indexed family. -/
theorem familyCovers_nestedDomain_iff (f : d ⟶ e) (U : Domain K d.algebra)
    {ι : Type v} (obj : ι → Domain K d.algebra) :
    (∀ x ∈ (nestedDomain f U).locus, ∃ i, x ∈ (nestedDomain f (obj i)).locus) ↔
      (∀ x ∈ U.locus, ∃ i, x ∈ (obj i).locus) := by
  simp only [nestedDomain_locus]
  constructor
  · intro h x hx
    obtain ⟨i, y, hy, heq⟩ := h (f.spectrumMap x) ⟨x, hx, rfl⟩
    exact ⟨i, f.isClosedEmbedding_spectrumMap.injective heq ▸ hy⟩
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨i, hi⟩ := h y hy
    exact ⟨i, y, hi, rfl⟩

/-- A finite cover transported through an actual nested chart inclusion. -/
def nestedFiniteCover (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) : Domain.FiniteCover (nestedDomain f U) where
  size := c.size
  obj i := nestedDomain f (c.obj i)
  map i := (nestedDomainFunctor f).map (c.map i)
  covers := (familyCovers_nestedDomain_iff f U c.obj).2 c.covers

@[simp] theorem nestedFiniteCover_size (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) : (nestedFiniteCover f c).size = c.size := rfl

@[simp] theorem nestedFiniteCover_obj (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (i : Fin c.size) :
    (nestedFiniteCover f c).obj i = nestedDomain f (c.obj i) := rfl

@[simp] theorem nestedFiniteCover_obj_algebra (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCover f c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCover_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCover f c).map i).restriction = (c.map i).restriction := rfl

@[simp] theorem nestedFiniteCover_singleton (f : d ⟶ e) (U : Domain K d.algebra) :
    nestedFiniteCover f (Domain.FiniteCover.singleton U) =
      Domain.FiniteCover.singleton (nestedDomain f U) := rfl

/-- Each actual quotient-spectrum triangle commutes over the target comparison. -/
theorem nestedFiniteCover_componentMap (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (i : Fin c.size) :
    (nestedFiniteCover f c).componentMap i =
      (nestedDomainLocusHomeomorph f U :
        C(U.locus, (nestedDomain f U).locus)).comp (c.componentMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The actual disjoint union of component spectra is unchanged. -/
theorem nestedFiniteCover_totalMap (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    (nestedFiniteCover f c).totalMap =
      (nestedDomainLocusHomeomorph f U :
        C(U.locus, (nestedDomain f U).locus)).comp c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, (nestedDomain f U).locus) => g x.2)
    (nestedFiniteCover_componentMap f c x.1)

/-- Refinement transport retains the chosen index and actual bounded map. -/
def nestedCoverRefinement (f : d ⟶ e) {U : Domain K d.algebra}
    {b c : Domain.FiniteCover U} (r : Refinement b c) :
    Refinement (nestedFiniteCover f b) (nestedFiniteCover f c) where
  index := r.index
  map i := (nestedDomainFunctor f).map (r.map i)

@[simp] theorem nestedCoverRefinement_index (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (nestedCoverRefinement f r).index = r.index := rfl

@[simp] theorem nestedCoverRefinement_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (i : Fin b.size) :
    ((nestedCoverRefinement f r).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem nestedCoverRefinement_spectrumMap (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (nestedCoverRefinement f r).spectrumMap = r.spectrumMap := rfl

/-- The functor on finite covers and their actual chosen-index refinements. -/
def nestedFiniteCoverFunctor (f : d ⟶ e) (U : Domain K d.algebra) :
    Domain.FiniteCover U ⥤ Domain.FiniteCover (nestedDomain f U) where
  obj c := nestedFiniteCover f c
  map r := nestedCoverRefinement f r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Fullness retains the index and uses the constructed hom preimage on domains. -/
def fullyFaithfulNestedFiniteCover (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedFiniteCoverFunctor f U).FullyFaithful where
  preimage r := {
    index := r.index
    map i := (fullyFaithfulNestedDomain f).preimage (r.map i) }
  map_preimage _ := Refinement.ext rfl
  preimage_map _ := Refinement.ext rfl

instance (f : d ⟶ e) (U : Domain K d.algebra) : (nestedFiniteCoverFunctor f U).Full :=
  (fullyFaithfulNestedFiniteCover f U).full

instance (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedFiniteCoverFunctor f U).Faithful :=
  (fullyFaithfulNestedFiniteCover f U).faithful

@[simp] theorem fullyFaithfulNestedFiniteCover_preimage_index (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U}
    (r : Refinement (nestedFiniteCover f b) (nestedFiniteCover f c)) :
    ((fullyFaithfulNestedFiniteCover f U).preimage r).index = r.index := rfl

@[simp] theorem fullyFaithfulNestedFiniteCover_preimage_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U}
    (r : Refinement (nestedFiniteCover f b) (nestedFiniteCover f c)) (i : Fin b.size) :
    (((fullyFaithfulNestedFiniteCover f U).preimage r).map i).restriction =
      (r.map i).restriction := rfl

/-- Extend an arbitrary outer cover and restore the original ambient target.
The component algebras and maps are retained, without an image-cover witness. -/
def nestedAmbientFiniteCover (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover (nestedDomain f U)) :
    Domain.FiniteCover (d.extendDomain U) where
  size := c.size
  obj i := e.extendDomain (c.obj i)
  map i := e.extendDomainFunctor.map (c.map i) ≫ (extendNestedDomainIso f U).hom
  covers x hx := (e.extendFiniteCover c).covers x
    ((Domain.locus_eq_of_iso (extendNestedDomainIso f U)).symm ▸ hx)

/-- Transport the same refinement between the ambiently restored covers. -/
def nestedAmbientFiniteCoverFunctor (f : d ⟶ e) (U : Domain K d.algebra) :
    Domain.FiniteCover (nestedDomain f U) ⥤ Domain.FiniteCover (d.extendDomain U) where
  obj c := nestedAmbientFiniteCover f c
  map r := {
    index := r.index
    map i := e.extendDomainFunctor.map (r.map i) }
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- After restoring the ambient target, nested cover transport agrees with
direct extension, componentwise by the actual domain comparison. -/
def nestedAmbientExtendCoverIso (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    nestedAmbientFiniteCover f (nestedFiniteCover f c) ≅ d.extendFiniteCover c where
  hom := {
    index := fun i => i
    map i := (extendNestedDomainIso f (c.obj i)).hom }
  inv := {
    index := fun i => i
    map i := (extendNestedDomainIso f (c.obj i)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

def nestedAmbientExtensionNatIso (f : d ⟶ e) (U : Domain K d.algebra) :
    nestedFiniteCoverFunctor f U ⋙ nestedAmbientFiniteCoverFunctor f U ≅
      d.extendFiniteCoverFunctor U :=
  NatIso.ofComponents (nestedAmbientExtendCoverIso f)
    (by intro b c r; apply Refinement.ext; rfl)

/-- Localize the ambiently restored cover and restore the original inner target. -/
def nestedFiniteCoverInverse (f : d ⟶ e) (U : Domain K d.algebra) :
    Domain.FiniteCover (nestedDomain f U) ⥤ Domain.FiniteCover U :=
  nestedAmbientFiniteCoverFunctor f U ⋙ d.restrictExtendedFiniteCoverFunctor U

@[simp] theorem nestedFiniteCoverInverse_obj_size (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U)) :
    ((nestedFiniteCoverInverse f U).obj c).size = c.size := rfl

@[simp] theorem nestedFiniteCoverInverse_obj_algebra (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    (((nestedFiniteCoverInverse f U).obj c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverInverse_obj_baseMap (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    (((nestedFiniteCoverInverse f U).obj c).obj i).baseMap =
      (c.map i).restriction.comp U.baseMap := rfl

@[simp] theorem nestedFiniteCoverInverse_obj_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    (((nestedFiniteCoverInverse f U).obj c).map i).restriction =
      (c.map i).restriction := rfl

@[simp] theorem nestedFiniteCoverInverse_map_index (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) :
    ((nestedFiniteCoverInverse f U).map r).index = r.index := rfl

@[simp] theorem nestedFiniteCoverInverse_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) (i : Fin b.size) :
    (((nestedFiniteCoverInverse f U).map r).map i).restriction =
      (r.map i).restriction := rfl

@[simp] theorem nestedFiniteCoverInverse_map_spectrumMap (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) :
    ((nestedFiniteCoverInverse f U).map r).spectrumMap = r.spectrumMap := rfl

/-- The inner round trip keeps each index and uses identity bounded maps. -/
def nestedFiniteCoverUnitIso (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    c ≅ (nestedFiniteCoverInverse f U).obj (nestedFiniteCover f c) where
  hom := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap⟩ }
  inv := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap.symm⟩ }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- The outer round trip applies to every supplied cover of the transported
domain, and uses the original component equation over its actual target. -/
def nestedFiniteCoverCounitIso (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover (nestedDomain f U)) :
    nestedFiniteCover f ((nestedFiniteCoverInverse f U).obj c) ≅ c where
  hom := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap.symm⟩ }
  inv := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap⟩ }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

@[simp] theorem nestedFiniteCoverUnitIso_hom_index (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverUnitIso f c).hom.index = id := rfl

@[simp] theorem nestedFiniteCoverUnitIso_inv_index (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    (nestedFiniteCoverUnitIso f c).inv.index = id := rfl

@[simp] theorem nestedFiniteCoverUnitIso_hom_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverUnitIso f c).hom.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverUnitIso_inv_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (i : Fin c.size) :
    ((nestedFiniteCoverUnitIso f c).inv.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverCounitIso_hom_index (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U)) :
    (nestedFiniteCoverCounitIso f c).hom.index = id := rfl

@[simp] theorem nestedFiniteCoverCounitIso_inv_index (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U)) :
    (nestedFiniteCoverCounitIso f c).inv.index = id := rfl

@[simp] theorem nestedFiniteCoverCounitIso_hom_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    ((nestedFiniteCoverCounitIso f c).hom.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

@[simp] theorem nestedFiniteCoverCounitIso_inv_map_restriction (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    ((nestedFiniteCoverCounitIso f c).inv.map i).restriction =
      BoundedAlgHom.id K (c.obj i).algebra := rfl

/-- Actual refinement categories of finite full-domain covers agree through
the nested chart, with a constructed inverse on arbitrary outer covers. -/
def nestedFiniteCoverEquivalence (f : d ⟶ e) (U : Domain K d.algebra) :
    Domain.FiniteCover U ≌ Domain.FiniteCover (nestedDomain f U) where
  functor := nestedFiniteCoverFunctor f U
  inverse := nestedFiniteCoverInverse f U
  unitIso := NatIso.ofComponents (nestedFiniteCoverUnitIso f)
    (by intro b c r; apply Refinement.ext; rfl)
  counitIso := NatIso.ofComponents (nestedFiniteCoverCounitIso f)
    (by intro b c r; apply Refinement.ext; rfl)
  functor_unitIso_comp c := Refinement.ext rfl

/-- The inverse's retained component spectrum triangle commutes over the
forward target homeomorphism by the original cover's base-map equation. -/
theorem nestedFiniteCoverInverse_componentMap (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) :
    (nestedDomainLocusHomeomorph f U :
      C(U.locus, (nestedDomain f U).locus)).comp
        (((nestedFiniteCoverInverse f U).obj c).componentMap i) =
      c.componentMap i := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun q : BoundedAlgHom K e.algebra (c.obj i).algebra => x (q a))
    (c.map i).comp_baseMap

theorem nestedFiniteCoverInverse_totalMap (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U)) :
    (nestedDomainLocusHomeomorph f U :
      C(U.locus, (nestedDomain f U).locus)).comp
        ((nestedFiniteCoverInverse f U).obj c).totalMap = c.totalMap := by
  apply ContinuousMap.ext
  intro x
  exact congrArg
    (fun g : C(BanachSpectrum (c.obj x.1).algebra, (nestedDomain f U).locus) => g x.2)
    (nestedFiniteCoverInverse_componentMap f c x.1)

@[simp] theorem nestedCoverRefinement_toSingleton (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    nestedCoverRefinement f (Refinement.toSingleton c) =
      Refinement.toSingleton (nestedFiniteCover f c) := Refinement.ext rfl

/-- Retained refinement spectra commute over the actual target homeomorphism. -/
theorem nestedCoverRefinement_spectrumMap_over_target (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (nestedFiniteCover f c).totalMap.comp (nestedCoverRefinement f r).spectrumMap =
      (nestedDomainLocusHomeomorph f U :
        C(U.locus, (nestedDomain f U).locus)).comp b.totalMap := by
  rw [(nestedCoverRefinement f r).spectrumMap_over_target, nestedFiniteCover_totalMap]

/-- The inverse refinement square also uses the unchanged quotient spectra. -/
theorem nestedFiniteCoverInverse_spectrumMap_over_target (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) :
    (nestedDomainLocusHomeomorph f U :
      C(U.locus, (nestedDomain f U).locus)).comp
        (((nestedFiniteCoverInverse f U).obj c).totalMap.comp
          ((nestedFiniteCoverInverse f U).map r).spectrumMap) = b.totalMap := by
  rw [((nestedFiniteCoverInverse f U).map r).spectrumMap_over_target,
    nestedFiniteCoverInverse_totalMap]

/-- Composition of a cover with covers of its components is preserved
literally, including the chosen finite enumeration and bounded composites. -/
theorem nestedFiniteCover_bind (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (b : ∀ i : Fin c.size, Domain.FiniteCover (c.obj i)) :
    nestedFiniteCover f (c.bind b) =
      (nestedFiniteCover f c).bind (fun i => nestedFiniteCover f (b i)) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
