import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverRefinement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverFamilyNaturality

/-! # Refinement naturality of continuous families under rational localization -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
variable {Y : Type v} [TopologicalSpace Y]

/-- Extension commutes with actual refinement restriction for all families. -/
theorem extendCoverFamily_pullbackFamily (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.extendCoverFamily b (r.pullbackFamily g) =
      (d.extendCoverRefinement r).pullbackFamily (d.extendCoverFamily c g) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g (r.index i))
    (d.extendDomainLocusHomeomorph_symm_naturality (r.map i) x).symm

/-- The extension square on the compatible-family subtypes. -/
theorem extendCoverFamilyEquiv_pullback (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (g : CompatibleFamily c Y) :
    d.extendCoverFamilyEquiv b (r.pullback g) =
      (d.extendCoverRefinement r).pullback (d.extendCoverFamilyEquiv c g) := by
  apply Subtype.ext
  exact d.extendCoverFamily_pullbackFamily r g.val

/-- Equality of the two composite equivalences in the extension square. -/
theorem pullbackEquiv_trans_extendCoverFamilyEquiv (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c) :
    (r.pullbackEquiv (Y := Y)).trans (d.extendCoverFamilyEquiv b) =
      (d.extendCoverFamilyEquiv c).trans
        ((d.extendCoverRefinement r).pullbackEquiv (Y := Y)) := by
  apply Equiv.ext
  intro g
  exact d.extendCoverFamilyEquiv_pullback r g

/-- Extension also commutes with descent from the finer cover, whose
inverse refinement equivalence glues and then restricts. -/
theorem extendCoverFamilyEquiv_pullbackEquiv_symm (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (g : CompatibleFamily b Y) :
    d.extendCoverFamilyEquiv c ((r.pullbackEquiv (Y := Y)).symm g) =
      ((d.extendCoverRefinement r).pullbackEquiv (Y := Y)).symm
        (d.extendCoverFamilyEquiv b g) := by
  apply ((d.extendCoverRefinement r).pullbackEquiv (Y := Y)).injective
  change (d.extendCoverRefinement r).pullback
      (d.extendCoverFamilyEquiv c ((r.pullbackEquiv (Y := Y)).symm g)) =
    (d.extendCoverRefinement r).pullbackEquiv
      (((d.extendCoverRefinement r).pullbackEquiv (Y := Y)).symm
        (d.extendCoverFamilyEquiv b g))
  rw [← d.extendCoverFamilyEquiv_pullback]
  change d.extendCoverFamilyEquiv b
      ((r.pullbackEquiv (Y := Y)) ((r.pullbackEquiv (Y := Y)).symm g)) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The extension square agrees on the unchanged actual component spectra. -/
theorem extendCoverFamily_spectrumFamilyMap_pullbackFamily (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover U} (r : Refinement b c)
    (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (d.extendFiniteCover b).spectrumFamilyMap
        ((d.extendCoverRefinement r).pullbackFamily (d.extendCoverFamily c g)) =
      (c.spectrumFamilyMap g).comp r.spectrumMap := by
  rw [← d.extendCoverFamily_pullbackFamily,
    d.extendCoverFamily_spectrumFamilyMap, r.spectrumFamilyMap_pullbackFamily]

/-- Restriction's component comparisons commute with the supplied actual
refinement arrows, with their chosen component indices retained. -/
theorem restrictCoverRefinement_locusMap (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) (i : Fin b.size)
    (x : ((d.restrictFiniteCover f b).obj i).locus) :
    d.restrictDomainLocusHomeomorph (c.obj (r.index i)) (c.map (r.index i) ≫ f)
        (((d.restrictCoverRefinement f r).map i).locusMap x) =
      (r.map i).locusMap
        (d.restrictDomainLocusHomeomorph (b.obj i) (b.map i ≫ f) x) :=
  Subtype.ext rfl

/-- Restriction commutes with actual refinement restriction for all families. -/
theorem restrictCoverFamily_pullbackFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    d.restrictCoverFamily f b (r.pullbackFamily g) =
      (d.restrictCoverRefinement f r).pullbackFamily (d.restrictCoverFamily f c g) := by
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg (g (r.index i)) (d.restrictCoverRefinement_locusMap f r i x).symm

/-- The restriction square on the actual compatible-family subtypes. -/
theorem restrictCoverFamilyEquiv_pullback (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) (g : CompatibleFamily c Y) :
    d.restrictCoverFamilyEquiv f b (r.pullback g) =
      (d.restrictCoverRefinement f r).pullback (d.restrictCoverFamilyEquiv f c g) := by
  apply Subtype.ext
  exact d.restrictCoverFamily_pullbackFamily f r g.val

/-- Equality of the two composite equivalences in the restriction square. -/
theorem pullbackEquiv_trans_restrictCoverFamilyEquiv (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) :
    (r.pullbackEquiv (Y := Y)).trans (d.restrictCoverFamilyEquiv f b) =
      (d.restrictCoverFamilyEquiv f c).trans
        ((d.restrictCoverRefinement f r).pullbackEquiv (Y := Y)) := by
  apply Equiv.ext
  intro g
  exact d.restrictCoverFamilyEquiv_pullback f r g

/-- Restriction commutes with the actual gluing-and-restriction inverse
of refinement pullback. -/
theorem restrictCoverFamilyEquiv_pullbackEquiv_symm (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) (g : CompatibleFamily b Y) :
    d.restrictCoverFamilyEquiv f c ((r.pullbackEquiv (Y := Y)).symm g) =
      ((d.restrictCoverRefinement f r).pullbackEquiv (Y := Y)).symm
        (d.restrictCoverFamilyEquiv f b g) := by
  apply ((d.restrictCoverRefinement f r).pullbackEquiv (Y := Y)).injective
  change (d.restrictCoverRefinement f r).pullback
      (d.restrictCoverFamilyEquiv f c ((r.pullbackEquiv (Y := Y)).symm g)) =
    (d.restrictCoverRefinement f r).pullbackEquiv
      (((d.restrictCoverRefinement f r).pullbackEquiv (Y := Y)).symm
        (d.restrictCoverFamilyEquiv f b g))
  rw [← d.restrictCoverFamilyEquiv_pullback]
  change d.restrictCoverFamilyEquiv f b
      ((r.pullbackEquiv (Y := Y)) ((r.pullbackEquiv (Y := Y)).symm g)) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Restriction and refinement assembly agree on the actual component spectra. -/
theorem restrictCoverFamily_spectrumFamilyMap_pullbackFamily (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) {b c : Domain.FiniteCover V}
    (r : Refinement b c) (g : ∀ i : Fin c.size, C((c.obj i).locus, Y)) :
    (d.restrictFiniteCover f b).spectrumFamilyMap
        ((d.restrictCoverRefinement f r).pullbackFamily (d.restrictCoverFamily f c g)) =
      (c.spectrumFamilyMap g).comp r.spectrumMap := by
  rw [← d.restrictCoverFamily_pullbackFamily,
    d.restrictCoverFamily_spectrumFamilyMap, r.spectrumFamilyMap_pullbackFamily]

/-- Rational extension of compatible continuous families is natural in the
actual chosen-index finite-cover category. -/
def extendCoverFamilyNatIso (d : RationalChart K A) (U : Domain K d.algebra)
    (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf U Y ≅
      (d.extendFiniteCoverFunctor U).op ⋙
        compatibleFamilyPresheaf (d.extendDomain U) Y :=
  NatIso.ofComponents (fun c => (d.extendCoverFamilyEquiv c.unop).toIso)
    (by
      intro b c r
      ext g
      exact d.extendCoverFamilyEquiv_pullback r.unop g)

@[simp] theorem extendCoverFamilyNatIso_hom_app (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : CompatibleFamily c Y) :
    (d.extendCoverFamilyNatIso U Y).hom.app (Opposite.op c) g =
      d.extendCoverFamilyEquiv c g := rfl

@[simp] theorem extendCoverFamilyNatIso_inv_app (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : CompatibleFamily (d.extendFiniteCover c) Y) :
    (d.extendCoverFamilyNatIso U Y).inv.app (Opposite.op c) g =
      (d.extendCoverFamilyEquiv c).symm g := rfl

/-- The extension natural isomorphism commutes with the concrete
global restriction and quotient-gluing components. -/
theorem extendCoverFamilyNatIso_gluing (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U) (g : C(U.locus, Y)) :
    (d.extendCoverFamilyNatIso U Y).hom.app (Opposite.op c)
        ((gluingNatIso U Y).hom.app (Opposite.op c) g) =
      (gluingNatIso (d.extendDomain U) Y).hom.app
        (Opposite.op (d.extendFiniteCover c))
        (g.comp ((d.extendDomainLocusHomeomorph U).symm :
          C((d.extendDomain U).locus, U.locus))) :=
  d.extendCoverFamilyEquiv_gluingEquiv c g

/-- Rational restriction gives a natural isomorphism of compatible-family
presheaves along the actual restricted-cover functor. -/
def restrictCoverFamilyNatIso (d : RationalChart K A) {V : Domain K A}
    (f : V ⟶ d.toDomain) (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf V Y ≅
      (d.restrictFiniteCoverFunctor f).op ⋙
        compatibleFamilyPresheaf (d.restrictDomain V f) Y :=
  NatIso.ofComponents (fun c => (d.restrictCoverFamilyEquiv f c.unop).toIso)
    (by
      intro b c r
      ext g
      exact d.restrictCoverFamilyEquiv_pullback f r.unop g)

@[simp] theorem restrictCoverFamilyNatIso_hom_app (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : CompatibleFamily c Y) :
    (d.restrictCoverFamilyNatIso f Y).hom.app (Opposite.op c) g =
      d.restrictCoverFamilyEquiv f c g := rfl

@[simp] theorem restrictCoverFamilyNatIso_inv_app (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : CompatibleFamily (d.restrictFiniteCover f c) Y) :
    (d.restrictCoverFamilyNatIso f Y).inv.app (Opposite.op c) g =
      (d.restrictCoverFamilyEquiv f c).symm g := rfl

/-- The restriction natural isomorphism commutes with the actual
global restriction and quotient-gluing components. -/
theorem restrictCoverFamilyNatIso_gluing (d : RationalChart K A)
    {V : Domain K A} (f : V ⟶ d.toDomain) (c : Domain.FiniteCover V)
    (g : C(V.locus, Y)) :
    (d.restrictCoverFamilyNatIso f Y).hom.app (Opposite.op c)
        ((gluingNatIso V Y).hom.app (Opposite.op c) g) =
      (gluingNatIso (d.restrictDomain V f) Y).hom.app
        (Opposite.op (d.restrictFiniteCover f c))
        (g.comp (d.restrictDomainLocusHomeomorph V f :
          C((d.restrictDomain V f).locus, V.locus))) :=
  d.restrictCoverFamilyEquiv_gluingEquiv f c g

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
