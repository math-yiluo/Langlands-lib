import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCoverFamilyNaturality

/-! # Continuous descent along the actual rational cover equivalence -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Domain.FiniteCover

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
variable {Y : Type v} [TopologicalSpace Y]

/-- Restriction of compatible families on an arbitrary ambient cover, with
the target restored to the original inner domain. -/
def restrictExtendedCoverFamilyEquiv (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U)) :
    CompatibleFamily c Y ≃ CompatibleFamily (d.restrictExtendedFiniteCover c) Y :=
  d.restrictCoverFamilyEquiv (d.extendDomainInclusion U) c

/-- Restoring the target changes neither local maps nor overlap agreement. -/
@[simp] theorem restrictExtendedCoverFamilyEquiv_val (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily c Y) :
    (d.restrictExtendedCoverFamilyEquiv c g).val =
      d.restrictCoverFamily (d.extendDomainInclusion U) c g.val := rfl

@[simp] theorem restrictExtendedCoverFamilyEquiv_symm_val (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily (d.restrictExtendedFiniteCover c) Y) :
    ((d.restrictExtendedCoverFamilyEquiv c).symm g).val =
      d.restrictCoverFamilyInverse (d.extendDomainInclusion U) c g.val := rfl

/-- The inverse cover functor's actual refinements commute with family restriction. -/
theorem restrictExtendedCoverFamilyEquiv_pullback (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (d.extendDomain U)}
    (r : Refinement b c) (g : CompatibleFamily c Y) :
    d.restrictExtendedCoverFamilyEquiv b (r.pullback g) =
      ((d.restrictExtendedFiniteCoverFunctor U).map r).pullback
        (d.restrictExtendedCoverFamilyEquiv c g) :=
  d.restrictCoverFamilyEquiv_pullback (d.extendDomainInclusion U) r g

/-- The same comparison commutes with the constructed gluing-and-restriction
inverse of refinement pullback. -/
theorem restrictExtendedCoverFamilyEquiv_pullbackEquiv_symm (d : RationalChart K A)
    {U : Domain K d.algebra} {b c : Domain.FiniteCover (d.extendDomain U)}
    (r : Refinement b c) (g : CompatibleFamily b Y) :
    d.restrictExtendedCoverFamilyEquiv c ((r.pullbackEquiv (Y := Y)).symm g) =
      (((d.restrictExtendedFiniteCoverFunctor U).map r).pullbackEquiv
        (Y := Y)).symm (d.restrictExtendedCoverFamilyEquiv b g) := by
  apply (((d.restrictExtendedFiniteCoverFunctor U).map r).pullbackEquiv
    (Y := Y)).injective
  change ((d.restrictExtendedFiniteCoverFunctor U).map r).pullback
      (d.restrictExtendedCoverFamilyEquiv c ((r.pullbackEquiv (Y := Y)).symm g)) =
    ((d.restrictExtendedFiniteCoverFunctor U).map r).pullbackEquiv
      ((((d.restrictExtendedFiniteCoverFunctor U).map r).pullbackEquiv
        (Y := Y)).symm (d.restrictExtendedCoverFamilyEquiv b g))
  rw [← d.restrictExtendedCoverFamilyEquiv_pullback]
  change d.restrictExtendedCoverFamilyEquiv b
      ((r.pullbackEquiv (Y := Y)) ((r.pullbackEquiv (Y := Y)).symm g)) = _
  rw [Equiv.apply_symm_apply]
  exact (((d.restrictExtendedFiniteCoverFunctor U).map r).pullbackEquiv
    (Y := Y)).apply_symm_apply (d.restrictExtendedCoverFamilyEquiv b g) |>.symm

/-- Component assembly is unchanged on the actual retained quotient spectra. -/
theorem restrictExtendedCoverFamilyEquiv_spectrumFamilyMap (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily c Y) :
    (d.restrictExtendedFiniteCover c).spectrumFamilyMap
        (d.restrictExtendedCoverFamilyEquiv c g).val = c.spectrumFamilyMap g.val :=
  d.restrictCoverFamily_spectrumFamilyMap (d.extendDomainInclusion U) c g.val

/-- Global restriction now uses the forward comparison from the original
inner locus, rather than from the unreconciled round-trip target. -/
theorem restrictExtendedCoverFamilyEquiv_gluingEquiv (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : C((d.extendDomain U).locus, Y)) :
    d.restrictExtendedCoverFamilyEquiv c (c.gluingEquiv g) =
      (d.restrictExtendedFiniteCover c).gluingEquiv
        (g.comp (d.extendDomainLocusHomeomorph U :
          C(U.locus, (d.extendDomain U).locus))) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  exact congrArg g (Subtype.ext rfl)

/-- Actual quotient gluing of the restricted family agrees over the restored
inner target with the original quotient gluing. -/
theorem glue_restrictExtendedCoverFamily (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily c Y) :
    (d.restrictExtendedFiniteCover c).glue
        (d.restrictExtendedCoverFamilyEquiv c g).val
        (d.restrictExtendedCoverFamilyEquiv c g).property =
      (c.glue g.val g.property).comp (d.extendDomainLocusHomeomorph U :
        C(U.locus, (d.extendDomain U).locus)) := by
  have h := d.restrictExtendedCoverFamilyEquiv_gluingEquiv c
    (c.glue g.val g.property)
  change d.restrictExtendedCoverFamilyEquiv c
    ((c.gluingEquiv (Y := Y)) ((c.gluingEquiv (Y := Y)).symm g)) = _ at h
  rw [Equiv.apply_symm_apply] at h
  apply ((d.restrictExtendedFiniteCover c).gluingEquiv (Y := Y)).injective
  exact ((d.restrictExtendedFiniteCover c).gluingEquiv
    (Y := Y)).apply_symm_apply (d.restrictExtendedCoverFamilyEquiv c g) |>.trans h

/-- Compatible continuous families compare naturally along the actual inverse
of the finite-cover localization equivalence, for every ambient cover. -/
def restrictExtendedCoverFamilyNatIso (d : RationalChart K A)
    (U : Domain K d.algebra) (Y : Type v) [TopologicalSpace Y] :
    compatibleFamilyPresheaf (d.extendDomain U) Y ≅
      (d.finiteCoverLocalizationEquivalence U).inverse.op ⋙
        compatibleFamilyPresheaf U Y :=
  NatIso.ofComponents (fun c => (d.restrictExtendedCoverFamilyEquiv c.unop).toIso)
    (by
      intro b c r
      ext g
      exact d.restrictExtendedCoverFamilyEquiv_pullback r.unop g)

@[simp] theorem restrictExtendedCoverFamilyNatIso_hom_app (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily c Y) :
    (d.restrictExtendedCoverFamilyNatIso U Y).hom.app (Opposite.op c) g =
      d.restrictExtendedCoverFamilyEquiv c g := rfl

@[simp] theorem restrictExtendedCoverFamilyNatIso_inv_app (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily (d.restrictExtendedFiniteCover c) Y) :
    (d.restrictExtendedCoverFamilyNatIso U Y).inv.app (Opposite.op c) g =
      (d.restrictExtendedCoverFamilyEquiv c).symm g := rfl

/-- The inverse-functor natural isomorphism commutes with the actual global
restriction components of the quotient-gluing natural isomorphisms. -/
theorem restrictExtendedCoverFamilyNatIso_gluing (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : C((d.extendDomain U).locus, Y)) :
    (d.restrictExtendedCoverFamilyNatIso U Y).hom.app (Opposite.op c)
        ((gluingNatIso (d.extendDomain U) Y).hom.app (Opposite.op c) g) =
      (gluingNatIso U Y).hom.app (Opposite.op (d.restrictExtendedFiniteCover c))
        (g.comp (d.extendDomainLocusHomeomorph U :
          C(U.locus, (d.extendDomain U).locus))) :=
  d.restrictExtendedCoverFamilyEquiv_gluingEquiv c g

/-- Restricting an extended family is exactly presheaf pullback through the
inverse unit of the actual cover-category equivalence. -/
theorem restrictExtendedCoverFamilyEquiv_extend_unit (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover U)
    (g : CompatibleFamily c Y) :
    d.restrictExtendedCoverFamilyEquiv (d.extendFiniteCover c)
        (d.extendCoverFamilyEquiv c g) =
      ((d.finiteCoverLocalizationEquivalence U).unitIso.inv.app c).pullback g := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  apply congrArg (g.val i)
  apply (d.extendDomainLocusHomeomorph (c.obj i)).injective
  exact ((d.extendDomainLocusHomeomorph (c.obj i)).apply_symm_apply _).trans
    (Subtype.ext rfl)

/-- Extending a restricted arbitrary ambient family is exactly pullback
through the counit of the actual cover-category equivalence. -/
theorem extend_restrictExtendedCoverFamilyEquiv_counit (d : RationalChart K A)
    {U : Domain K d.algebra} (c : Domain.FiniteCover (d.extendDomain U))
    (g : CompatibleFamily c Y) :
    d.extendCoverFamilyEquiv (d.restrictExtendedFiniteCover c)
        (d.restrictExtendedCoverFamilyEquiv c g) =
      ((d.finiteCoverLocalizationEquivalence U).counitIso.hom.app c).pullback g := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro x
  apply congrArg (g.val i)
  exact Subtype.ext (d.extendDomainLocusHomeomorph_symm_spectrumMap
    ((d.restrictExtendedFiniteCover c).obj i) x)

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
