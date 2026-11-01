import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEmbeddedCoverLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Finite-cover refinement localization at a specified embedded domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  (d : Domain K A) (hd : Function.Injective d.spectrumMap)

namespace Refinement

/-- Extension retains each chosen index and actual bounded restriction. -/
def extendOfInjective {U : Domain K d.algebra} {c e : FiniteCover U}
    (r : Refinement e c) :
    Refinement (d.extendFiniteCoverOfInjective hd e)
      (d.extendFiniteCoverOfInjective hd c) where
  index := r.index
  map i := (d.extendOfInjectiveFunctor hd).map (r.map i)

@[simp] theorem extendOfInjective_index {U : Domain K d.algebra}
    {c e : FiniteCover U} (r : Refinement e c) :
    (extendOfInjective d hd r).index = r.index := rfl

@[simp] theorem extendOfInjective_map_restriction {U : Domain K d.algebra}
    {c e : FiniteCover U} (r : Refinement e c) (i : Fin e.size) :
    ((extendOfInjective d hd r).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem extendOfInjective_spectrumMap {U : Domain K d.algebra}
    {c e : FiniteCover U} (r : Refinement e c) :
    (extendOfInjective d hd r).spectrumMap = r.spectrumMap := rfl

/-- Relative passage retains chosen indices and uses the original commuting
bounded inclusion triangles over the specified containing domain. -/
def relativeOfInjective {V : Domain K A} (f : V ⟶ d)
    {c e : FiniteCover V} (r : Refinement e c) :
    Refinement (d.relativeFiniteCoverOfInjective hd f e)
      (d.relativeFiniteCoverOfInjective hd f c) where
  index := r.index
  map i := d.relativeFunctor.map
    (show Over.mk (e.map i ≫ f) ⟶ Over.mk (c.map (r.index i) ≫ f) from
      Over.homMk (r.map i)
        ((inferInstance : Subsingleton (Inclusion (e.obj i) d)).elim _ _))

@[simp] theorem relativeOfInjective_index {V : Domain K A} (f : V ⟶ d)
    {c e : FiniteCover V} (r : Refinement e c) :
    (relativeOfInjective d hd f r).index = r.index := rfl

@[simp] theorem relativeOfInjective_map_restriction {V : Domain K A}
    (f : V ⟶ d) {c e : FiniteCover V} (r : Refinement e c) (i : Fin e.size) :
    ((relativeOfInjective d hd f r).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem relativeOfInjective_spectrumMap {V : Domain K A} (f : V ⟶ d)
    {c e : FiniteCover V} (r : Refinement e c) :
    (relativeOfInjective d hd f r).spectrumMap = r.spectrumMap := rfl

end Refinement

/-- Extend finite covers and every chosen refinement along the actual embedding. -/
def extendFunctorOfInjective (U : Domain K d.algebra) :
    FiniteCover U ⥤ FiniteCover (d.extendOfInjective hd U) where
  obj := d.extendFiniteCoverOfInjective hd
  map r := Refinement.extendOfInjective d hd r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Restrict finite covers and chosen refinements to the actual containing algebra. -/
def relativeFunctorOfInjective {V : Domain K A} (f : V ⟶ d) :
    FiniteCover V ⥤ FiniteCover (d.relative V f) where
  obj := d.relativeFiniteCoverOfInjective hd f
  map r := Refinement.relativeOfInjective d hd f r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Restrict an arbitrary cover of the extended target and restore the original
target through its concrete domain round-trip isomorphism. -/
def extensionInverseObjOfInjective {U : Domain K d.algebra}
    (c : FiniteCover (d.extendOfInjective hd U)) : FiniteCover U where
  size := c.size
  obj i := d.relative (c.obj i) (c.map i ≫ d.extendOfInjectiveInclusion hd U)
  map i := d.relativeInclusion (c.map i) (d.extendOfInjectiveInclusion hd U) ≫
    (d.relativeExtendOfInjectiveIso hd U).hom
  covers x hx :=
    (d.relativeFiniteCoverOfInjective hd (d.extendOfInjectiveInclusion hd U) c).covers x
      (by simpa only [d.relative_extendOfInjective_locus hd U] using hx)

/-- The inverse retains every chosen component index and bounded restriction. -/
def extensionInverseOfInjective (U : Domain K d.algebra) :
    FiniteCover (d.extendOfInjective hd U) ⥤ FiniteCover U where
  obj := extensionInverseObjOfInjective d hd
  map {c e} r := {
    index := r.index
    map i := d.relativeFunctor.map
      (show Over.mk (c.map i ≫ d.extendOfInjectiveInclusion hd U) ⟶
        Over.mk (e.map (r.index i) ≫ d.extendOfInjectiveInclusion hd U) from
          Over.homMk (r.map i)
            ((inferInstance : Subsingleton (Inclusion (c.obj i) d)).elim _ _)) }
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

@[simp] theorem extensionInverseOfInjective_map_index (U : Domain K d.algebra)
    {c e : FiniteCover (d.extendOfInjective hd U)} (r : e ⟶ c) :
    ((extensionInverseOfInjective d hd U).map r).index = r.index := rfl

@[simp] theorem extensionInverseOfInjective_map_restriction (U : Domain K d.algebra)
    {c e : FiniteCover (d.extendOfInjective hd U)} (r : e ⟶ c) (i : Fin e.size) :
    (((extensionInverseOfInjective d hd U).map r).map i).restriction =
      (r.map i).restriction := rfl

@[simp] theorem extensionInverseOfInjective_spectrumMap (U : Domain K d.algebra)
    {c e : FiniteCover (d.extendOfInjective hd U)} (r : e ⟶ c) :
    ((extensionInverseOfInjective d hd U).map r).spectrumMap = r.spectrumMap := rfl

/-- The unit uses the same component indices and identity bounded algebra maps;
the original component inclusion equation proves each relative base equation. -/
def extensionUnitIsoOfInjective {U : Domain K d.algebra} (c : FiniteCover U) :
    c ≅ (extensionInverseOfInjective d hd U).obj
      ((extendFunctorOfInjective d hd U).obj c) where
  hom := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, by
      change (c.map i).restriction.comp U.baseMap = (c.obj i).baseMap
      exact (c.map i).comp_baseMap⟩ }
  inv := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, by
      change (c.obj i).baseMap = (c.map i).restriction.comp U.baseMap
      exact (c.map i).comp_baseMap.symm⟩ }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- The counit uses the actual ambient-domain round-trip isomorphism on each
retained component, with identity index functions in both directions. -/
def extensionCounitIsoOfInjective (U : Domain K d.algebra)
    (c : FiniteCover (d.extendOfInjective hd U)) :
    (extendFunctorOfInjective d hd U).obj
      ((extensionInverseOfInjective d hd U).obj c) ≅ c where
  hom := {
    index := fun i => i
    map i := (d.extendRelativeOfInjectiveIso hd (c.obj i)
      (c.map i ≫ d.extendOfInjectiveInclusion hd U)).hom }
  inv := {
    index := fun i => i
    map i := (d.extendRelativeOfInjectiveIso hd (c.obj i)
      (c.map i ≫ d.extendOfInjectiveInclusion hd U)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- Finite actual full-domain covers and their chosen-index refinements
localize equivalently along a specified embedded full domain. -/
def localizationEquivalenceOfInjective (U : Domain K d.algebra) :
    FiniteCover U ≌ FiniteCover (d.extendOfInjective hd U) where
  functor := extendFunctorOfInjective d hd U
  inverse := extensionInverseOfInjective d hd U
  unitIso := NatIso.ofComponents (extensionUnitIsoOfInjective d hd)
    (by intro c e r; apply Refinement.ext; rfl)
  counitIso := NatIso.ofComponents (extensionCounitIsoOfInjective d hd U)
    (by intro c e r; apply Refinement.ext; rfl)
  functor_unitIso_comp _ := Refinement.ext rfl

/-- The inverse cover's actual total spectrum map agrees with the original
one over the spectrum-induced homeomorphism of the target loci. -/
theorem extensionInverseObjOfInjective_totalMap {U : Domain K d.algebra}
    (c : FiniteCover (d.extendOfInjective hd U)) :
    (d.extendOfInjectiveLocusHomeomorph hd U :
      C(U.locus, (d.extendOfInjective hd U).locus)).comp
        (extensionInverseObjOfInjective d hd c).totalMap = c.totalMap := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (c.map x.1 ≫ d.extendOfInjectiveInclusion hd U).spectrumMap_over_base x.2

/-- The extended chosen refinement remains over the actual original target
locus diagram through the specified spectrum-induced homeomorphism. -/
theorem extendOfInjective_spectrumMap_over_target {U : Domain K d.algebra}
    {c e : FiniteCover U} (r : Refinement e c) :
    (d.extendFiniteCoverOfInjective hd c).totalMap.comp
        (Refinement.extendOfInjective d hd r).spectrumMap =
      (d.extendOfInjectiveLocusHomeomorph hd U :
        C(U.locus, (d.extendOfInjective hd U).locus)).comp e.totalMap := by
  rw [(Refinement.extendOfInjective d hd r).spectrumMap_over_target,
    d.extendFiniteCoverOfInjective_totalMap hd e]

/-- Relative refinement remains over the original target locus through the
specified spectrum-induced relative-locus homeomorphism. -/
theorem relativeOfInjective_spectrumMap_over_target {V : Domain K A}
    (f : V ⟶ d) {c e : FiniteCover V} (r : Refinement e c) :
    (d.relativeLocusHomeomorphOfInjective hd V f :
      C((d.relative V f).locus, V.locus)).comp
        ((d.relativeFiniteCoverOfInjective hd f c).totalMap.comp
          (Refinement.relativeOfInjective d hd f r).spectrumMap) =
      e.totalMap := by
  rw [(Refinement.relativeOfInjective d hd f r).spectrumMap_over_target,
    d.relativeFiniteCoverOfInjective_totalMap hd f e]

@[simp] theorem extendOfInjective_toSingleton {U : Domain K d.algebra}
    (c : FiniteCover U) :
    Refinement.extendOfInjective d hd (Refinement.toSingleton c) =
      Refinement.toSingleton (d.extendFiniteCoverOfInjective hd c) :=
  Refinement.ext rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
