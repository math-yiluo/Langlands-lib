import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNestedCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverDescentEquivalence

/-! # Continuous families through nested actual rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {d e : RationalChart K A}
variable {Y : Type v} [TopologicalSpace Y]

/-- The inverse locus comparison lifts the actual outer spectrum point. -/
theorem nestedDomainLocusHomeomorph_symm_spectrumMap (f : d ⟶ e)
    (U : Domain K d.algebra) (x : (nestedDomain f U).locus) :
    f.spectrumMap ((nestedDomainLocusHomeomorph f U).symm x) = x :=
  congrArg (fun z : (nestedDomain f U).locus => (z : BanachSpectrum e.algebra))
    ((nestedDomainLocusHomeomorph f U).apply_symm_apply x)

/-- Inverse component comparisons commute with the retained restrictions. -/
theorem nestedDomainLocusHomeomorph_symm_naturality (f : d ⟶ e)
    {U V : Domain K d.algebra} (k : U ⟶ V) (x : (nestedDomain f U).locus) :
    (nestedDomainLocusHomeomorph f V).symm
        (((nestedDomainFunctor f).map k).locusMap x) =
      k.locusMap ((nestedDomainLocusHomeomorph f U).symm x) := by
  apply (nestedDomainLocusHomeomorph f V).injective
  exact ((nestedDomainLocusHomeomorph f V).apply_symm_apply _).trans
    ((nestedDomainLocusHomeomorph_naturality f k
      ((nestedDomainLocusHomeomorph f U).symm x)).trans
        (congrArg ((nestedDomainFunctor f).map k).locusMap
          ((nestedDomainLocusHomeomorph f U).apply_symm_apply x))).symm

/-- Transport each continuous map by the inverse actual component homeomorphism. -/
def nestedCoverFamily (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    ∀ i : Fin (nestedFiniteCover f c).size,
      C(((nestedFiniteCover f c).obj i).locus, Y) :=
  fun i => (g i).comp ((nestedDomainLocusHomeomorph f (c.obj i)).symm :
    C((nestedDomain f (c.obj i)).locus, (c.obj i).locus))

/-- The inverse family uses the forward actual component homeomorphisms. -/
def nestedCoverFamilyInverse (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (nestedFiniteCover f c).size,
      C(((nestedFiniteCover f c).obj i).locus, Y)) :
    ∀ i : Fin c.size, C((c.obj i).locus, Y) :=
  fun i => (g i).comp (nestedDomainLocusHomeomorph f (c.obj i) :
    C((c.obj i).locus, (nestedDomain f (c.obj i)).locus))

theorem compatible_nestedCoverFamily (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y))
    (hg : c.Compatible g) :
    (nestedFiniteCover f c).Compatible (nestedCoverFamily f c g) := by
  intro i j x y h
  apply hg i j
  apply f.isClosedEmbedding_spectrumMap.injective
  exact (nestedDomainLocusHomeomorph_symm_spectrumMap f (c.obj i) x).trans
    (h.trans (nestedDomainLocusHomeomorph_symm_spectrumMap f (c.obj j) y).symm)

theorem compatible_nestedCoverFamilyInverse (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (nestedFiniteCover f c).size,
      C(((nestedFiniteCover f c).obj i).locus, Y))
    (hg : (nestedFiniteCover f c).Compatible g) :
    c.Compatible (nestedCoverFamilyInverse f c g) := by
  intro i j x y h
  exact hg i j _ _ (congrArg f.spectrumMap h)

@[simp] theorem nestedCoverFamilyInverse_nestedCoverFamily (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    nestedCoverFamilyInverse f c (nestedCoverFamily f c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i) ((nestedDomainLocusHomeomorph f (c.obj i)).symm_apply_apply x)

@[simp] theorem nestedCoverFamily_nestedCoverFamilyInverse (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin (nestedFiniteCover f c).size,
      C(((nestedFiniteCover f c).obj i).locus, Y)) :
    nestedCoverFamily f c (nestedCoverFamilyInverse f c g) = g := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g i) ((nestedDomainLocusHomeomorph f (c.obj i)).apply_symm_apply x)

/-- Nested chart transport gives a constructed equivalence of compatible families. -/
def nestedCoverFamilyEquiv (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) :
    CompatibleFamily c Y ≃ CompatibleFamily (nestedFiniteCover f c) Y where
  toFun g := ⟨nestedCoverFamily f c g.val, compatible_nestedCoverFamily f c g.val g.property⟩
  invFun g := ⟨nestedCoverFamilyInverse f c g.val,
    compatible_nestedCoverFamilyInverse f c g.val g.property⟩
  left_inv g := Subtype.ext (nestedCoverFamilyInverse_nestedCoverFamily f c g.val)
  right_inv g := Subtype.ext (nestedCoverFamily_nestedCoverFamilyInverse f c g.val)

/-- Global restriction agrees with componentwise nested transport. -/
theorem nestedCoverFamily_restrict (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (g : C(U.locus, Y)) :
    nestedCoverFamily f c (c.restrict g) =
      (nestedFiniteCover f c).restrict
        (g.comp ((nestedDomainLocusHomeomorph f U).symm :
          C((nestedDomain f U).locus, U.locus))) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg g (nestedDomainLocusHomeomorph_symm_naturality f (c.map i) x).symm

theorem nestedCoverFamilyEquiv_gluingEquiv (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : C(U.locus, Y)) :
    nestedCoverFamilyEquiv f c (c.gluingEquiv g) =
      (nestedFiniteCover f c).gluingEquiv
        (g.comp ((nestedDomainLocusHomeomorph f U).symm :
          C((nestedDomain f U).locus, U.locus))) :=
  Subtype.ext (nestedCoverFamily_restrict f c g)

/-- The glued map transforms by the actual inverse target homeomorphism. -/
theorem glue_nestedCoverFamily (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover U) (g : CompatibleFamily c Y) :
    (nestedFiniteCover f c).glue (nestedCoverFamilyEquiv f c g).val
        (nestedCoverFamilyEquiv f c g).property =
      (c.glue g.val g.property).comp ((nestedDomainLocusHomeomorph f U).symm :
        C((nestedDomain f U).locus, U.locus)) := by
  apply ((nestedFiniteCover f c).glue_unique _ _ _ ?_).symm
  intro i
  rw [← nestedCoverFamily_restrict f c (c.glue g.val g.property)]
  change (c.restrict (c.glue g.val g.property) i).comp _ = (g.val i).comp _
  exact congrArg (fun h : C((c.obj i).locus, Y) => h.comp
    ((nestedDomainLocusHomeomorph f (c.obj i)).symm :
      C((nestedDomain f (c.obj i)).locus, (c.obj i).locus)))
    (c.restrict_glue g.val g.property i)

/-- Assembly on the retained disjoint union of quotient spectra is unchanged. -/
theorem nestedCoverFamily_spectrumFamilyMap (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (nestedFiniteCover f c).spectrumFamilyMap (nestedCoverFamily f c g) =
      c.spectrumFamilyMap g := by
  apply ContinuousMap.ext
  intro x
  apply congrArg (g x.1)
  exact (congrArg (nestedDomainLocusHomeomorph f (c.obj x.1)).symm
    (nestedDomain_spectrumToLocus f (c.obj x.1) x.2)).trans
    ((nestedDomainLocusHomeomorph f (c.obj x.1)).symm_apply_apply _)

/-- Transport commutes with every actual refinement, before overlap agreement. -/
theorem nestedCoverFamily_pullbackFamily (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U}
    (r : Refinement b c) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    nestedCoverFamily f b (r.pullbackFamily g) =
      (nestedCoverRefinement f r).pullbackFamily (nestedCoverFamily f c g) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g (r.index i))
    (nestedDomainLocusHomeomorph_symm_naturality f (r.map i) x).symm

theorem nestedCoverFamilyEquiv_pullback (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U}
    (r : Refinement b c) (g : CompatibleFamily c Y) :
    nestedCoverFamilyEquiv f b (r.pullback g) =
      (nestedCoverRefinement f r).pullback (nestedCoverFamilyEquiv f c g) :=
  Subtype.ext (nestedCoverFamily_pullbackFamily f r g.val)

/-- Refinement naturality also holds as an equality of constructed equivalences. -/
theorem pullbackEquiv_trans_nestedCoverFamilyEquiv (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (r.pullbackEquiv (Y := Y)).trans (nestedCoverFamilyEquiv f b) =
      (nestedCoverFamilyEquiv f c).trans
        ((nestedCoverRefinement f r).pullbackEquiv (Y := Y)) := by
  apply Equiv.ext
  intro g
  exact nestedCoverFamilyEquiv_pullback f r g

/-- Nested transport commutes with the gluing-and-restriction inverse
of refinement pullback. -/
theorem nestedCoverFamilyEquiv_pullbackEquiv_symm (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (g : CompatibleFamily b Y) :
    nestedCoverFamilyEquiv f c ((r.pullbackEquiv (Y := Y)).symm g) =
      ((nestedCoverRefinement f r).pullbackEquiv (Y := Y)).symm
        (nestedCoverFamilyEquiv f b g) := by
  apply ((nestedCoverRefinement f r).pullbackEquiv (Y := Y)).injective
  exact (nestedCoverFamilyEquiv_pullback f r
    ((r.pullbackEquiv (Y := Y)).symm g)).symm.trans
      ((congrArg (nestedCoverFamilyEquiv f b)
        ((r.pullbackEquiv (Y := Y)).apply_symm_apply g)).trans
          (((nestedCoverRefinement f r).pullbackEquiv (Y := Y)).apply_symm_apply
            (nestedCoverFamilyEquiv f b g)).symm)

/-- Compatible families compare naturally along the actual nested-cover functor. -/
def nestedCoverFamilyNatIso (f : d ⟶ e) (U : Domain K d.algebra)
    (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf U Y ≅
      (nestedFiniteCoverFunctor f U).op ⋙
        compatibleFamilyPresheaf (nestedDomain f U) Y :=
  NatIso.ofComponents (fun c => (nestedCoverFamilyEquiv f c.unop).toIso)
    (by
      intro b c r
      ext g
      exact nestedCoverFamilyEquiv_pullback f r.unop g)

@[simp] theorem nestedCoverFamilyNatIso_hom_app (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : CompatibleFamily c Y) :
    (nestedCoverFamilyNatIso f U Y).hom.app (Opposite.op c) g =
      nestedCoverFamilyEquiv f c g := rfl

@[simp] theorem nestedCoverFamilyNatIso_inv_app (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : CompatibleFamily (nestedFiniteCover f c) Y) :
    (nestedCoverFamilyNatIso f U Y).inv.app (Opposite.op c) g =
      (nestedCoverFamilyEquiv f c).symm g := rfl

/-- The natural isomorphism agrees with the actual quotient-gluing components. -/
theorem nestedCoverFamilyNatIso_gluing (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : C(U.locus, Y)) :
    (nestedCoverFamilyNatIso f U Y).hom.app (Opposite.op c)
        ((gluingNatIso U Y).hom.app (Opposite.op c) g) =
      (gluingNatIso (nestedDomain f U) Y).hom.app
        (Opposite.op (nestedFiniteCover f c))
        (g.comp ((nestedDomainLocusHomeomorph f U).symm :
          C((nestedDomain f U).locus, U.locus))) :=
  nestedCoverFamilyEquiv_gluingEquiv f c g

/-- The arbitrary-cover inverse compares each component by actual ambient
extension followed by localization, without an image-cover assumption. -/
def nestedInverseComponentLocusHomeomorph (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover (nestedDomain f U)) (i : Fin c.size) :
    (((nestedFiniteCoverInverse f U).obj c).obj i).locus ≃ₜ (c.obj i).locus :=
  (d.restrictDomainLocusHomeomorph ((nestedAmbientFiniteCover f c).obj i)
    ((nestedAmbientFiniteCover f c).map i ≫ d.extendDomainInclusion U)).trans
      (e.extendDomainLocusHomeomorph (c.obj i)).symm

/-- This component comparison is the restriction of the actual chart map. -/
theorem nestedInverseComponentLocusHomeomorph_apply_coe (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (i : Fin c.size) (x : (((nestedFiniteCoverInverse f U).obj c).obj i).locus) :
    (nestedInverseComponentLocusHomeomorph f c i x : BanachSpectrum e.algebra) =
      f.spectrumMap x := by
  apply e.spectrumMap_injective
  exact (e.extendDomainLocusHomeomorph_symm_spectrumMap (c.obj i)
    (d.restrictDomainLocusHomeomorph ((nestedAmbientFiniteCover f c).obj i)
      ((nestedAmbientFiniteCover f c).map i ≫ d.extendDomainInclusion U) x)).trans
    (f.spectrumMap_over_base x).symm

/-- Construct continuous-family transport for every cover of the outer domain. -/
def nestedInverseCoverFamilyEquiv (f : d ⟶ e) {U : Domain K d.algebra}
    (c : Domain.FiniteCover (nestedDomain f U)) :
    CompatibleFamily c Y ≃ CompatibleFamily ((nestedFiniteCoverInverse f U).obj c) Y :=
  (e.extendCoverFamilyEquiv c).trans
    (d.restrictExtendedCoverFamilyEquiv (nestedAmbientFiniteCover f c))

/-- Every inverse-transported local map is composition with the constructed
component homeomorphism. -/
@[simp] theorem nestedInverseCoverFamilyEquiv_val (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily c Y) (i : Fin c.size) :
    (nestedInverseCoverFamilyEquiv f c g).val i =
      (g.val i).comp (nestedInverseComponentLocusHomeomorph f c i :
        C((((nestedFiniteCoverInverse f U).obj c).obj i).locus, (c.obj i).locus)) := rfl

/-- The inverse equivalence also uses actual component homeomorphisms. -/
@[simp] theorem nestedInverseCoverFamilyEquiv_symm_val (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily ((nestedFiniteCoverInverse f U).obj c) Y) (i : Fin c.size) :
    ((nestedInverseCoverFamilyEquiv f c).symm g).val i =
      (g.val i).comp ((nestedInverseComponentLocusHomeomorph f c i).symm :
        C((c.obj i).locus, (((nestedFiniteCoverInverse f U).obj c).obj i).locus)) := rfl

/-- Inverse chart transport commutes with every supplied refinement. -/
theorem nestedInverseCoverFamilyEquiv_pullback (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) (g : CompatibleFamily c Y) :
    nestedInverseCoverFamilyEquiv f b (r.pullback g) =
      ((nestedFiniteCoverInverse f U).map r).pullback
        (nestedInverseCoverFamilyEquiv f c g) := by
  exact (congrArg (d.restrictExtendedCoverFamilyEquiv (nestedAmbientFiniteCover f b))
    (e.extendCoverFamilyEquiv_pullback r g)).trans
      (d.restrictExtendedCoverFamilyEquiv_pullback
        ((nestedAmbientFiniteCoverFunctor f U).map r) (e.extendCoverFamilyEquiv c g))

/-- The inverse refinement square is also an equality of equivalences. -/
theorem pullbackEquiv_trans_nestedInverseCoverFamilyEquiv (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) :
    (r.pullbackEquiv (Y := Y)).trans (nestedInverseCoverFamilyEquiv f b) =
      (nestedInverseCoverFamilyEquiv f c).trans
        (((nestedFiniteCoverInverse f U).map r).pullbackEquiv (Y := Y)) := by
  apply Equiv.ext
  intro g
  exact nestedInverseCoverFamilyEquiv_pullback f r g

/-- The arbitrary-cover inverse commutes with descent along refinements. -/
theorem nestedInverseCoverFamilyEquiv_pullbackEquiv_symm (f : d ⟶ e)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (nestedDomain f U)}
    (r : Refinement b c) (g : CompatibleFamily b Y) :
    nestedInverseCoverFamilyEquiv f c ((r.pullbackEquiv (Y := Y)).symm g) =
      (((nestedFiniteCoverInverse f U).map r).pullbackEquiv (Y := Y)).symm
        (nestedInverseCoverFamilyEquiv f b g) := by
  apply (((nestedFiniteCoverInverse f U).map r).pullbackEquiv (Y := Y)).injective
  exact (nestedInverseCoverFamilyEquiv_pullback f r
    ((r.pullbackEquiv (Y := Y)).symm g)).symm.trans
      ((congrArg (nestedInverseCoverFamilyEquiv f b)
        ((r.pullbackEquiv (Y := Y)).apply_symm_apply g)).trans
          ((((nestedFiniteCoverInverse f U).map r).pullbackEquiv (Y := Y)).apply_symm_apply
            (nestedInverseCoverFamilyEquiv f b g)).symm)

/-- Assembly of the inverse-transported family retains the actual spectra. -/
theorem nestedInverseCoverFamilyEquiv_spectrumFamilyMap (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily c Y) :
    ((nestedFiniteCoverInverse f U).obj c).spectrumFamilyMap
        (nestedInverseCoverFamilyEquiv f c g).val = c.spectrumFamilyMap g.val :=
  (d.restrictExtendedCoverFamilyEquiv_spectrumFamilyMap (nestedAmbientFiniteCover f c)
    (e.extendCoverFamilyEquiv c g)).trans
      (e.extendCoverFamily_spectrumFamilyMap c g.val)

/-- For every outer cover, inverse family transport agrees with restriction
of a global map along the actual forward target homeomorphism. -/
theorem nestedInverseCoverFamilyEquiv_gluingEquiv (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : C((nestedDomain f U).locus, Y)) :
    nestedInverseCoverFamilyEquiv f c (c.gluingEquiv g) =
      ((nestedFiniteCoverInverse f U).obj c).gluingEquiv
        (g.comp (nestedDomainLocusHomeomorph f U :
          C(U.locus, (nestedDomain f U).locus))) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg g (Subtype.ext (nestedInverseComponentLocusHomeomorph_apply_coe f c i x))

/-- Actual quotient gluing commutes with the arbitrary-cover inverse. -/
theorem glue_nestedInverseCoverFamily (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily c Y) :
    ((nestedFiniteCoverInverse f U).obj c).glue
        (nestedInverseCoverFamilyEquiv f c g).val
        (nestedInverseCoverFamilyEquiv f c g).property =
      (c.glue g.val g.property).comp (nestedDomainLocusHomeomorph f U :
        C(U.locus, (nestedDomain f U).locus)) := by
  have h := nestedInverseCoverFamilyEquiv_gluingEquiv f c (c.glue g.val g.property)
  change nestedInverseCoverFamilyEquiv f c
    ((c.gluingEquiv (Y := Y)) ((c.gluingEquiv (Y := Y)).symm g)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  apply (((nestedFiniteCoverInverse f U).obj c).gluingEquiv (Y := Y)).injective
  exact (((nestedFiniteCoverInverse f U).obj c).gluingEquiv (Y := Y)).apply_symm_apply
    (nestedInverseCoverFamilyEquiv f c g) |>.trans h

/-- Compatible families compare naturally along the constructed inverse
cover functor on all outer covers. -/
def nestedInverseCoverFamilyNatIso (f : d ⟶ e) (U : Domain K d.algebra)
    (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf (nestedDomain f U) Y ≅
      (nestedFiniteCoverInverse f U).op ⋙ compatibleFamilyPresheaf U Y :=
  NatIso.ofComponents (fun c => (nestedInverseCoverFamilyEquiv f c.unop).toIso)
    (by
      intro b c r
      ext g
      exact nestedInverseCoverFamilyEquiv_pullback f r.unop g)

@[simp] theorem nestedInverseCoverFamilyNatIso_hom_app (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily c Y) :
    (nestedInverseCoverFamilyNatIso f U Y).hom.app (Opposite.op c) g =
      nestedInverseCoverFamilyEquiv f c g := rfl

@[simp] theorem nestedInverseCoverFamilyNatIso_inv_app (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily ((nestedFiniteCoverInverse f U).obj c) Y) :
    (nestedInverseCoverFamilyNatIso f U Y).inv.app (Opposite.op c) g =
      (nestedInverseCoverFamilyEquiv f c).symm g := rfl

/-- The inverse natural isomorphism agrees with global quotient gluing. -/
theorem nestedInverseCoverFamilyNatIso_gluing (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : C((nestedDomain f U).locus, Y)) :
    (nestedInverseCoverFamilyNatIso f U Y).hom.app (Opposite.op c)
        ((gluingNatIso (nestedDomain f U) Y).hom.app (Opposite.op c) g) =
      (gluingNatIso U Y).hom.app
        (Opposite.op ((nestedFiniteCoverInverse f U).obj c))
        (g.comp (nestedDomainLocusHomeomorph f U :
          C(U.locus, (nestedDomain f U).locus))) :=
  nestedInverseCoverFamilyEquiv_gluingEquiv f c g

/-- The inner family round trip is exactly pullback through the inverse
unit of the actual nested-cover equivalence. -/
theorem nestedInverseCoverFamilyEquiv_nested_unit (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : CompatibleFamily c Y) :
    nestedInverseCoverFamilyEquiv f (nestedFiniteCover f c)
        (nestedCoverFamilyEquiv f c g) =
      ((nestedFiniteCoverEquivalence f U).unitIso.inv.app c).pullback g := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  apply congrArg (g.val i)
  apply (nestedDomainLocusHomeomorph f (c.obj i)).injective
  exact ((nestedDomainLocusHomeomorph f (c.obj i)).apply_symm_apply _).trans
    (Subtype.ext (nestedInverseComponentLocusHomeomorph_apply_coe f
      (nestedFiniteCover f c) i x))

/-- The outer family round trip is exactly pullback through the counit,
for every supplied outer cover. -/
theorem nested_nestedInverseCoverFamilyEquiv_counit (f : d ⟶ e)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (nestedDomain f U))
    (g : CompatibleFamily c Y) :
    nestedCoverFamilyEquiv f ((nestedFiniteCoverInverse f U).obj c)
        (nestedInverseCoverFamilyEquiv f c g) =
      ((nestedFiniteCoverEquivalence f U).counitIso.hom.app c).pullback g := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  apply congrArg (g.val i)
  apply Subtype.ext
  exact (nestedInverseComponentLocusHomeomorph_apply_coe f c i
    ((nestedDomainLocusHomeomorph f (((nestedFiniteCoverInverse f U).obj c).obj i)).symm
      x)).trans
    (nestedDomainLocusHomeomorph_symm_spectrumMap f
      (((nestedFiniteCoverInverse f U).obj c).obj i) x)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
