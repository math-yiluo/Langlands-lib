import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainOpenSections
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheafLocalization

/-! # Intrinsic and ambient rational sections under full-domain localization -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Opposite RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

/-- Intrinsic rational sections on a relative domain and ambient rational
sections on its original locus recover the same actual algebra element. -/
def relativeLocusSectionsEquiv (U : Over d) :
    OpenSections.Sections (d.relativeFunctor.obj U).locus ≃ₐ[K]
      OpenSections.Sections U.left.locus :=
  (locusSectionsEquiv (d.relativeFunctor.obj U)).symm.trans
    (locusSectionsEquiv U.left)

@[simp]
theorem relativeLocusSectionsEquiv_apply (U : Over d)
    (s : OpenSections.Sections (d.relativeFunctor.obj U).locus) :
    d.relativeLocusSectionsEquiv U s =
      toLocusSections U.left (fromLocusSections (d.relativeFunctor.obj U) s) := rfl

@[simp]
theorem relativeLocusSectionsEquiv_symm_apply (U : Over d)
    (s : OpenSections.Sections U.left.locus) :
    (d.relativeLocusSectionsEquiv U).symm s =
      toLocusSections (d.relativeFunctor.obj U) (fromLocusSections U.left s) := rfl

/-- The comparison retains the element on the unchanged algebra in both
rational-section presentations. -/
@[simp]
theorem relativeLocusSectionsEquiv_toLocusSections (U : Over d)
    (a : U.left.algebra) :
    d.relativeLocusSectionsEquiv U
        (toLocusSections (d.relativeFunctor.obj U) a) =
      toLocusSections U.left a := by
  exact congrArg (toLocusSections U.left)
    (fromLocusSections_toLocusSections (d.relativeFunctor.obj U) a)

@[simp]
theorem fromLocusSections_relativeLocusSectionsEquiv (U : Over d)
    (s : OpenSections.Sections (d.relativeFunctor.obj U).locus) :
    fromLocusSections U.left (d.relativeLocusSectionsEquiv U s) =
      fromLocusSections (d.relativeFunctor.obj U) s := by
  exact fromLocusSections_toLocusSections U.left _

/-- Every ambient quotient component is the original bounded restriction
of the recovered intrinsic element. -/
@[simp]
theorem relativeLocusSectionsEquiv_chart (U : Over d)
    (s : OpenSections.Sections (d.relativeFunctor.obj U).locus)
    (e : OpenSections.ChartIn U.left.locus) :
    (d.relativeLocusSectionsEquiv U s).val e =
      (inclusionOfSubset e.val.toDomain U.left e.property).restriction
        (fromLocusSections (d.relativeFunctor.obj U) s) := rfl

/-- Base elements over the containing algebra become the original ambient
bounded restriction, followed by its canonical section family. -/
theorem relativeLocusSectionsEquiv_fromBase (U : Over d) (a : d.algebra) :
    d.relativeLocusSectionsEquiv U
        (OpenSections.fromBase (d.relativeFunctor.obj U).locus a) =
      toLocusSections U.left (U.hom.restriction a) := by
  rw [← toLocusSections_baseMap (d.relativeFunctor.obj U)]
  exact d.relativeLocusSectionsEquiv_toLocusSections U (U.hom.restriction a)

/-- The intrinsic and ambient section comparisons commute with every
actual arrow in the ambient slice. -/
theorem relativeLocusSectionsEquiv_restriction {U V : Over d} (f : U ⟶ V)
    (s : OpenSections.Sections (d.relativeFunctor.obj V).locus) :
    d.relativeLocusSectionsEquiv U
        (OpenSections.restriction (d.relativeFunctor.map f).subset s) =
      OpenSections.restriction f.left.subset (d.relativeLocusSectionsEquiv V s) := by
  change toLocusSections U.left
      (fromLocusSections (d.relativeFunctor.obj U)
        (OpenSections.restriction (d.relativeFunctor.map f).subset s)) = _
  rw [← fromLocusSections_restriction (d.relativeFunctor.map f) s]
  exact toLocusSections_restriction f.left
    (fromLocusSections (d.relativeFunctor.obj V) s)

/-- The entire intrinsic rational-section presheaf on relative domains is
canonically the ambient rational-section presheaf on the slice. -/
def relativeLocusSectionPresheafIso :
    d.relativeFunctor.op ⋙ locusSectionPresheaf K d.algebra ≅
      (Over.forget d).op ⋙ locusSectionPresheaf K A :=
  NatIso.ofComponents
    (fun U => CommAlgCat.isoMk (d.relativeLocusSectionsEquiv U.unop))
    (by
      intro U V f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro s
      exact d.relativeLocusSectionsEquiv_restriction f.unop s)

@[simp]
theorem relativeLocusSectionPresheafIso_hom_app_apply (U : Over d)
    (s : OpenSections.Sections (d.relativeFunctor.obj U).locus) :
    (d.relativeLocusSectionPresheafIso).hom.app (op U) s =
      d.relativeLocusSectionsEquiv U s := rfl

@[simp]
theorem relativeLocusSectionPresheafIso_inv_app_apply (U : Over d)
    (s : OpenSections.Sections U.left.locus) :
    (d.relativeLocusSectionPresheafIso).inv.app (op U) s =
      (d.relativeLocusSectionsEquiv U).symm s := rfl

/-- Transport the actual intrinsic compatible-section sheaf through the
proved equivalence of finite-domain sites. -/
def relativeLocusSectionSheaf :
    Sheaf ((finiteDomainTopology K A).over d) (CommAlgCat K) :=
  (d.localizationSheafEquivalence (CommAlgCat K)).functor.obj
    (locusSectionSheaf K d.algebra)

/-- On the finite-domain slice, the transported intrinsic structure
sections agree with the actual ambient compatible rational sections. -/
def localizationLocusSectionSheafIso :
    d.relativeLocusSectionSheaf ≅ (locusSectionSheaf K A).over d :=
  ObjectProperty.isoMk _ d.relativeLocusSectionPresheafIso

@[simp]
theorem localizationLocusSectionSheafIso_hom_app_apply (U : Over d)
    (s : OpenSections.Sections (d.relativeFunctor.obj U).locus) :
    (d.localizationLocusSectionSheafIso).hom.hom.app (op U) s =
      d.relativeLocusSectionsEquiv U s := rfl

@[simp]
theorem localizationLocusSectionSheafIso_inv_app_apply (U : Over d)
    (s : OpenSections.Sections U.left.locus) :
    (d.localizationLocusSectionSheafIso).inv.hom.app (op U) s =
      (d.relativeLocusSectionsEquiv U).symm s := rfl

/-- Extending a full domain keeps its algebra, so its intrinsic and
ambient compatible families are canonically equivalent. -/
def extendLocusSectionsEquiv (U : Domain K d.algebra) :
    OpenSections.Sections U.locus ≃ₐ[K]
      OpenSections.Sections (d.extend U).locus :=
  (locusSectionsEquiv U).symm.trans (locusSectionsEquiv (d.extend U))

@[simp]
theorem extendLocusSectionsEquiv_apply (U : Domain K d.algebra)
    (s : OpenSections.Sections U.locus) :
    d.extendLocusSectionsEquiv U s =
      toLocusSections (d.extend U) (fromLocusSections U s) := rfl

@[simp]
theorem extendLocusSectionsEquiv_symm_apply (U : Domain K d.algebra)
    (s : OpenSections.Sections (d.extend U).locus) :
    (d.extendLocusSectionsEquiv U).symm s =
      toLocusSections U (fromLocusSections (d.extend U) s) := rfl

@[simp]
theorem extendLocusSectionsEquiv_toLocusSections (U : Domain K d.algebra)
    (a : U.algebra) :
    d.extendLocusSectionsEquiv U (toLocusSections U a) =
      toLocusSections (d.extend U) a := by
  change toLocusSections (d.extend U) (fromLocusSections U (toLocusSections U a)) = _
  rw [fromLocusSections_toLocusSections]

@[simp]
theorem fromLocusSections_extendLocusSectionsEquiv (U : Domain K d.algebra)
    (s : OpenSections.Sections U.locus) :
    fromLocusSections (d.extend U) (d.extendLocusSectionsEquiv U s) =
      fromLocusSections U s := by
  exact fromLocusSections_toLocusSections (d.extend U) _

/-- The extension comparison retains each actual ambient quotient component. -/
@[simp]
theorem extendLocusSectionsEquiv_chart (U : Domain K d.algebra)
    (s : OpenSections.Sections U.locus)
    (e : OpenSections.ChartIn (d.extend U).locus) :
    (d.extendLocusSectionsEquiv U s).val e =
      (inclusionOfSubset e.val.toDomain (d.extend U) e.property).restriction
        (fromLocusSections U s) := rfl

/-- Restriction from the containing domain is exactly the original
structural map of the inner domain, expressed as ambient sections. -/
theorem extendLocusSectionsEquiv_fromBase (U : Domain K d.algebra)
    (a : d.algebra) :
    d.extendLocusSectionsEquiv U (OpenSections.fromBase U.locus a) =
      toLocusSections (d.extend U) ((d.extendInclusion U).restriction a) := by
  rw [← toLocusSections_baseMap U]
  exact d.extendLocusSectionsEquiv_toLocusSections U (U.baseMap a)

theorem extendLocusSectionsEquiv_restriction {U V : Domain K d.algebra}
    (f : U ⟶ V) (s : OpenSections.Sections V.locus) :
    d.extendLocusSectionsEquiv U (OpenSections.restriction f.subset s) =
      OpenSections.restriction (d.extendFunctor.map f).subset
        (d.extendLocusSectionsEquiv V s) := by
  change toLocusSections (d.extend U)
      (fromLocusSections U (OpenSections.restriction f.subset s)) = _
  rw [← fromLocusSections_restriction f s]
  exact toLocusSections_restriction (d.extendFunctor.map f) (fromLocusSections V s)

/-- Returning from the ambient slice recovers the intrinsic rational-section
presheaf, with its actual component restrictions. -/
def extendLocusSectionPresheafIso :
    d.extendOverFunctor.op ⋙ (Over.forget d).op ⋙ locusSectionPresheaf K A ≅
      locusSectionPresheaf K d.algebra :=
  (NatIso.ofComponents
    (fun U => CommAlgCat.isoMk (d.extendLocusSectionsEquiv U.unop))
    (by
      intro U V f
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro s
      exact d.extendLocusSectionsEquiv_restriction f.unop s)).symm

@[simp]
theorem extendLocusSectionPresheafIso_hom_app_apply (U : Domain K d.algebra)
    (s : OpenSections.Sections (d.extend U).locus) :
    (d.extendLocusSectionPresheafIso).hom.app (op U) s =
      (d.extendLocusSectionsEquiv U).symm s := rfl

@[simp]
theorem extendLocusSectionPresheafIso_inv_app_apply (U : Domain K d.algebra)
    (s : OpenSections.Sections U.locus) :
    (d.extendLocusSectionPresheafIso).inv.app (op U) s =
      d.extendLocusSectionsEquiv U s := rfl

/-- The inverse finite-site equivalence sends the ambient compatible-section
sheaf localized at `d` to the actual intrinsic compatible-section sheaf. -/
def inverseLocalizationLocusSectionSheafIso :
    (d.localizationSheafEquivalence (CommAlgCat K)).inverse.obj
        ((locusSectionSheaf K A).over d) ≅
      locusSectionSheaf K d.algebra :=
  ObjectProperty.isoMk _ d.extendLocusSectionPresheafIso

@[simp]
theorem inverseLocalizationLocusSectionSheafIso_hom_app_apply
    (U : Domain K d.algebra)
    (s : OpenSections.Sections (d.extend U).locus) :
    (d.inverseLocalizationLocusSectionSheafIso).hom.hom.app (op U) s =
      (d.extendLocusSectionsEquiv U).symm s := rfl

@[simp]
theorem inverseLocalizationLocusSectionSheafIso_inv_app_apply
    (U : Domain K d.algebra) (s : OpenSections.Sections U.locus) :
    (d.inverseLocalizationLocusSectionSheafIso).inv.hom.app (op U) s =
      d.extendLocusSectionsEquiv U s := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
