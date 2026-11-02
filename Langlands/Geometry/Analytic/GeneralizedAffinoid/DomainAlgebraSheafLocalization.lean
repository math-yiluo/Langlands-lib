import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSiteLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraSheaf

/-! # Localization of the actual stored full-domain algebra sheaf -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory Opposite

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

/-- Relative domains retain the entire bounded algebra presheaf on the
ambient slice. -/
theorem relative_boundedPresheaf :
    d.relativeFunctor.op ⋙ boundedPresheaf K d.algebra =
      (Over.forget d).op ⋙ boundedPresheaf K A := rfl

/-- The relative algebra presheaf has exactly the ambient stored objects
and restriction maps. -/
theorem relative_algebraPresheaf :
    d.relativeFunctor.op ⋙ algebraPresheaf K d.algebra =
      (Over.forget d).op ⋙ algebraPresheaf K A := rfl

/-- The finite-site localization equivalence applied to the actual
algebra sheaf over the containing domain's algebra. -/
def relativeAlgebraSheaf :
    Sheaf ((finiteDomainTopology K A).over d) (CommAlgCat K) :=
  (d.localizationSheafEquivalence (CommAlgCat K)).functor.obj
    (algebraSheaf K d.algebra)

@[simp]
theorem relativeAlgebraSheaf_obj (U : Over d) :
    (d.relativeAlgebraSheaf).obj.obj (op U) =
      CommAlgCat.of K U.left.algebra := rfl

@[simp]
theorem relativeAlgebraSheaf_map_apply {U V : Over d} (f : U ⟶ V)
    (a : V.left.algebra) :
    (d.relativeAlgebraSheaf).obj.map f.op a = f.left.restriction a := rfl

/-- The transported sheaf is the ambient stored algebra sheaf localized
at `d`. Both directions act by the identity on the unchanged algebras. -/
def localizationAlgebraSheafIso :
    d.relativeAlgebraSheaf ≅ (algebraSheaf K A).over d :=
  ObjectProperty.isoMk _ (Iso.refl _)

@[simp]
theorem localizationAlgebraSheafIso_hom_apply (U : Over d)
    (a : U.left.algebra) :
    (d.localizationAlgebraSheafIso).hom.hom.app (op U) a = a := rfl

@[simp]
theorem localizationAlgebraSheafIso_inv_apply (U : Over d)
    (a : U.left.algebra) :
    (d.localizationAlgebraSheafIso).inv.hom.app (op U) a = a := rfl

/-- The localized structural map is precisely restriction from the
containing domain, as a map on every original section. -/
@[simp]
theorem localizationAlgebraSheafIso_hom_baseMap (U : Over d)
    (a : d.algebra) :
    (d.localizationAlgebraSheafIso).hom.hom.app (op U)
        ((d.relativeFunctor.obj U).baseMap a) =
      U.hom.restriction a := rfl

@[simp]
theorem localizationAlgebraSheafIso_inv_restriction (U : Over d)
    (a : d.algebra) :
    (d.localizationAlgebraSheafIso).inv.hom.app (op U)
        (U.hom.restriction a) =
      (d.relativeFunctor.obj U).baseMap a := rfl

/-- Returning from the slice also retains the entire bounded presheaf,
not merely the underlying sets of sections. -/
theorem extend_boundedPresheaf :
    d.extendOverFunctor.op ⋙ (Over.forget d).op ⋙ boundedPresheaf K A =
      boundedPresheaf K d.algebra := rfl

theorem extend_algebraPresheaf :
    d.extendOverFunctor.op ⋙ (Over.forget d).op ⋙ algebraPresheaf K A =
      algebraPresheaf K d.algebra := rfl

/-- The inverse finite-site equivalence sends the localized ambient
stored sheaf back to the original stored algebra sheaf over `d.algebra`. -/
def inverseLocalizationAlgebraSheafIso :
    (d.localizationSheafEquivalence (CommAlgCat K)).inverse.obj
        ((algebraSheaf K A).over d) ≅
      algebraSheaf K d.algebra :=
  ObjectProperty.isoMk _ (Iso.refl _)

@[simp]
theorem inverseLocalizationAlgebraSheafIso_hom_apply
    (U : Domain K d.algebra) (a : U.algebra) :
    (d.inverseLocalizationAlgebraSheafIso).hom.hom.app (op U) a = a := rfl

@[simp]
theorem inverseLocalizationAlgebraSheafIso_inv_apply
    (U : Domain K d.algebra) (a : U.algebra) :
    (d.inverseLocalizationAlgebraSheafIso).inv.hom.app (op U) a = a := rfl

/-- Restriction along the actual extension's inclusion is the original
structural map over `d.algebra`, also after the inverse comparison. -/
@[simp]
theorem inverseLocalizationAlgebraSheafIso_hom_restriction
    (U : Domain K d.algebra) (a : d.algebra) :
    (d.inverseLocalizationAlgebraSheafIso).hom.hom.app (op U)
        ((d.extendInclusion U).restriction a) =
      U.baseMap a := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
