import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactLocal
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof

/-! # Geometric inputs to compact analytic étale sections -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable [hT2 : T2Space (localizedSpaceFunctor.obj X)]
variable {R : Type (max u (v + 1) uL)} [CommRing R]

include h hT2

/-- The supplied point axioms give lifting over every étale neighborhood on
a Hausdorff analytic space, using étaleness of open domains. -/
theorem etalePointLifting_of_hausdorff : EtalePointLifting L (X := X) :=
  etalePointLifting_of_openDomains L h (etaleOpenDomainStatement X)

/-- On a Hausdorff analytic space, global field-valued support is the full
inverse image of its underlying-point support. -/
theorem support_etaleSelf_eq_preimage_of_hausdorff
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    support (etalePoints L h) F s =
      pointProjection L X ⁻¹' etaleUnderlyingSupport L h F s :=
  support_etaleSelf_eq_preimage L h
    (etalePointLifting_of_hausdorff L h) F s

/-- The actual underlying support is closed when every underlying point has
an L-valued representative. -/
theorem isClosed_etaleUnderlyingSupport_of_hausdorff
    (hX : Function.Surjective (pointProjection L X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    IsClosed (etaleUnderlyingSupport L h F s) :=
  isClosed_etaleUnderlyingSupport L h
    (etalePointLifting_of_hausdorff L h) hX
    (fun U => etaleOpenMap K U.hom U.prop) F s

/-- Compact support in field-valued points is compactness of the actual
underlying support on a Hausdorff analytic space with surjective projection. -/
theorem isCompactlySupported_etaleSelf_iff_isCompact_underlyingSupport_of_hausdorff
    (hX : Function.Surjective (pointProjection L X))
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R)
    (s : F.obj (op (etaleSelf X))) :
    letI := pointTopology L X
    IsCompactlySupported (etalePoints L h) F s ↔
      IsCompact (etaleUnderlyingSupport L h F s) :=
  isCompactlySupported_etaleSelf_iff_isCompact_underlyingSupport L h
    (etalePointLifting_of_hausdorff L h) hX
    (fun U => etaleOpenMap K U.hom U.prop) F s

variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)

/-- The canonical compact-section inclusion is an isomorphism under the
Hausdorff and point-surjectivity hypotheses. -/
theorem isIso_etaleCompactInclusion_of_hausdorff
    (hX : Function.Surjective (pointProjection L X)) :
    IsIso (etaleCompactInclusion L ρ h R) :=
  isIso_etaleCompactInclusion (R := R) L h ρ
    (etalePointLifting_of_hausdorff L h) hX
    (fun U => etaleOpenMap K U.hom U.prop)

/-- The canonical degree-zero compact comparison as a natural isomorphism
under the Hausdorff and point-surjectivity hypotheses. -/
def etaleCompactSectionsIsoOfHausdorff
    (hX : Function.Surjective (pointProjection L X)) :
    etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactSections L h R :=
  haveI := isIso_etaleCompactInclusion_of_hausdorff (R := R) L h ρ hX
  asIso (etaleCompactInclusion L ρ h R)

/-- The forward map is the published canonical compact-section inclusion. -/
theorem etaleCompactSectionsIsoOfHausdorff_hom
    (hX : Function.Surjective (pointProjection L X)) :
    (etaleCompactSectionsIsoOfHausdorff (R := R) L h ρ hX).hom =
      etaleCompactInclusion L ρ h R := rfl

end Langlands.Sheaf.Equivariant.Analytic
