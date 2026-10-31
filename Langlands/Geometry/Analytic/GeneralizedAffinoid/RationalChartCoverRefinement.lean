import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainCoverLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Finite-cover refinement categories inside actual rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Extension retains the chosen index and extends each actual restriction. -/
def extendCoverRefinement (d : RationalChart K A) {U : Domain K d.algebra}
    {b c : Domain.FiniteCover U} (r : Refinement b c) :
    Refinement (d.extendFiniteCover b) (d.extendFiniteCover c) where
  index := r.index
  map i := d.extendDomainFunctor.map (r.map i)

@[simp] theorem extendCoverRefinement_index (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (d.extendCoverRefinement r).index = r.index := rfl

@[simp] theorem extendCoverRefinement_map_restriction (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (i : Fin b.size) :
    ((d.extendCoverRefinement r).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem extendCoverRefinement_spectrumMap (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (d.extendCoverRefinement r).spectrumMap = r.spectrumMap := rfl

/-- Extension on actual covers and chosen-index refinements. -/
def extendFiniteCoverFunctor (d : RationalChart K A) (U : Domain K d.algebra) :
    Domain.FiniteCover U ⥤ Domain.FiniteCover (d.extendDomain U) where
  obj c := d.extendFiniteCover c
  map r := d.extendCoverRefinement r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- The actual refinement triangle supplies the equation over the rational
quotient for the same bounded component restriction. -/
def restrictCoverRefinement (d : RationalChart K A) {V : Domain K A}
    (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V} (r : Refinement b c) :
    Refinement (d.restrictFiniteCover f b) (d.restrictFiniteCover f c) where
  index := r.index
  map i := ⟨(r.map i).restriction, congrArg Domain.Inclusion.restriction
    (show r.map i ≫ (c.map (r.index i) ≫ f) = b.map i ≫ f from
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun g => g ≫ f) (r.over_target i)))⟩

@[simp] theorem restrictCoverRefinement_index (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain)
    {b c : Domain.FiniteCover V} (r : Refinement b c) :
    (d.restrictCoverRefinement f r).index = r.index := rfl

@[simp] theorem restrictCoverRefinement_map_restriction (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain)
    {b c : Domain.FiniteCover V} (r : Refinement b c) (i : Fin b.size) :
    ((d.restrictCoverRefinement f r).map i).restriction = (r.map i).restriction := rfl

@[simp] theorem restrictCoverRefinement_spectrumMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain)
    {b c : Domain.FiniteCover V} (r : Refinement b c) :
    (d.restrictCoverRefinement f r).spectrumMap = r.spectrumMap := rfl

/-- Restriction on actual covers and chosen-index refinements. -/
def restrictFiniteCoverFunctor (d : RationalChart K A) {V : Domain K A}
    (f : V ⟶ d.toDomain) :
    Domain.FiniteCover V ⥤ Domain.FiniteCover (d.restrictDomain V f) where
  obj c := d.restrictFiniteCover f c
  map r := d.restrictCoverRefinement f r
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- Restrict any ambient cover of an extended domain and restore the
original inner target using the actual round-trip domain isomorphism. -/
def restrictExtendedFiniteCover (d : RationalChart K A) {U : Domain K d.algebra}
    (c : Domain.FiniteCover (d.extendDomain U)) : Domain.FiniteCover U where
  size := c.size
  obj i := (d.restrictFiniteCover (d.extendDomainInclusion U) c).obj i
  map i := (d.restrictFiniteCover (d.extendDomainInclusion U) c).map i ≫
    (d.restrictExtendDomainIso U).hom
  covers x hx := (d.restrictFiniteCover (d.extendDomainInclusion U) c).covers x
    (by simpa only [d.restrict_extendDomain_locus U] using hx)

@[simp] theorem restrictExtendedFiniteCover_size (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U)) :
    (d.restrictExtendedFiniteCover c).size = c.size := rfl

@[simp] theorem restrictExtendedFiniteCover_obj_algebra (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (i : Fin c.size) :
    ((d.restrictExtendedFiniteCover c).obj i).algebra = (c.obj i).algebra := rfl

@[simp] theorem restrictExtendedFiniteCover_map_restriction (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (i : Fin c.size) :
    ((d.restrictExtendedFiniteCover c).map i).restriction =
      (c.map i).restriction := rfl

/-- The inverse on covers accepts arbitrary ambient components and retains
the actual bounded maps of every supplied refinement. -/
def restrictExtendedFiniteCoverFunctor (d : RationalChart K A)
    (U : Domain K d.algebra) :
    Domain.FiniteCover (d.extendDomain U) ⥤ Domain.FiniteCover U where
  obj c := d.restrictExtendedFiniteCover c
  map r := {
    index := r.index
    map i := (d.restrictCoverRefinement (d.extendDomainInclusion U) r).map i }
  map_id _ := Refinement.ext rfl
  map_comp _ _ := Refinement.ext rfl

/-- The inner cover round trip uses the same index and identity bounded
maps. Its structural equations are the original component restrictions. -/
def finiteCoverLocalizationUnitIso (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    c ≅ (d.restrictExtendedFiniteCoverFunctor U).obj
      ((d.extendFiniteCoverFunctor U).obj c) where
  hom := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap⟩ }
  inv := {
    index := fun i => i
    map i := ⟨BoundedAlgHom.id K (c.obj i).algebra, (c.map i).comp_baseMap.symm⟩ }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- The ambient cover round trip is the actual domain round trip on each
component, with the same chosen indices. -/
def finiteCoverLocalizationCounitIso (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U)) :
    (d.extendFiniteCoverFunctor U).obj
      ((d.restrictExtendedFiniteCoverFunctor U).obj c) ≅ c where
  hom := {
    index := fun i => i
    map i := (d.extendRestrictDomainIso (c.obj i)
      (c.map i ≫ d.extendDomainInclusion U)).hom }
  inv := {
    index := fun i => i
    map i := (d.extendRestrictDomainIso (c.obj i)
      (c.map i ≫ d.extendDomainInclusion U)).inv }
  hom_inv_id := Refinement.ext rfl
  inv_hom_id := Refinement.ext rfl

/-- The actual refinement categories of finite full-domain covers agree
over an inner domain and its extension to the original affinoid base. -/
def finiteCoverLocalizationEquivalence (d : RationalChart K A)
    (U : Domain K d.algebra) :
    Domain.FiniteCover U ≌ Domain.FiniteCover (d.extendDomain U) where
  functor := d.extendFiniteCoverFunctor U
  inverse := d.restrictExtendedFiniteCoverFunctor U
  unitIso := NatIso.ofComponents (d.finiteCoverLocalizationUnitIso)
    (by intro b c r; apply Refinement.ext; rfl)
  counitIso := NatIso.ofComponents (d.finiteCoverLocalizationCounitIso)
    (by intro b c r; apply Refinement.ext; rfl)
  functor_unitIso_comp c := Refinement.ext rfl

/-- The canonical arrow to the concrete singleton cover is preserved. -/
@[simp] theorem extendCoverRefinement_toSingleton (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) :
    d.extendCoverRefinement (Refinement.toSingleton c) =
      Refinement.toSingleton (d.extendFiniteCover c) := Refinement.ext rfl

@[simp] theorem restrictCoverRefinement_toSingleton (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V) :
    d.restrictCoverRefinement f (Refinement.toSingleton c) =
      Refinement.toSingleton (d.restrictFiniteCover f c) := Refinement.ext rfl

/-- Extension's unchanged refinement spectrum map lies over the target
locus homeomorphism already constructed for the actual cover. -/
theorem extendCoverRefinement_spectrumMap_over_target (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (d.extendFiniteCover c).totalMap.comp (d.extendCoverRefinement r).spectrumMap =
      (d.extendDomainLocusHomeomorph U :
        C(U.locus, (d.extendDomain U).locus)).comp b.totalMap := by
  rw [(d.extendCoverRefinement r).spectrumMap_over_target, d.extendFiniteCover_totalMap]

/-- Restriction's unchanged refinement spectrum map lies over the original
ambient target after its actual inverse-image locus homeomorphism. -/
theorem restrictCoverRefinement_spectrumMap_over_target (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain)
    {b c : Domain.FiniteCover V} (r : Refinement b c) :
    (d.restrictDomainLocusHomeomorph V f :
      C((d.restrictDomain V f).locus, V.locus)).comp
        ((d.restrictFiniteCover f c).totalMap.comp
          (d.restrictCoverRefinement f r).spectrumMap) = b.totalMap := by
  rw [(d.restrictCoverRefinement f r).spectrumMap_over_target, d.restrictFiniteCover_totalMap]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
