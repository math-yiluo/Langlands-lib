import Langlands.BruhatTits.IntegralModels.FacetRootDatumAssembly
import Langlands.BruhatTits.IntegralModels.FacetTorusQuotient
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetReflections

/-! # The remaining root comparison for a descended facet root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))
  (Q : SpecialFibreQuotientData D)
  (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
  (hT : T.IsClosedSplit) (hQ : Q.IsReductiveQuotient)
  (Droot : RelativeRootReflectionData P.i)
  (hroots : ∀ χ : characterLattice T.specialFibre,
    χ ∈ relativeRoots (T.specialFibreInclusion ≫ Q.projection) ↔
      (T.characterSpecialization hT.1).symm χ ∈
        facetDerivativeRoots P.toValuationBuildingData Fa)

include hA hR he hD hQ hroots

/-- The actual quotient root datum with its full specialized derivative graph.
The exact root-membership comparison is the only additional geometric input. -/
def unramifiedFacetRootDatumOfRootComparison :
    {RD : RootDatum (relativeRoots (T.specialFibreInclusion ≫ Q.projection))
        (characterLattice T.specialFibre) (cocharacterLattice T.specialFibre) //
      IsRootDatumOf (T.specialFibreInclusion ≫ Q.projection) RD ∧
        Set.range (fun k => (RD.root k, RD.coroot k)) =
          apartmentDerivativeRootCorootGraph P.toValuationBuildingData
            T Droot hT.1 Fa} := by
  apply apartmentDerivativeRootDatumOfRootComparison P.toValuationBuildingData
    Q T Droot hT.1 Fa hQ.2.2
    (T.isClosedSubgroup_quotientTorus Q hT hQ) hroots
  intro a ha
  obtain ⟨⟨n, σ⟩, hn, hσ⟩ :=
    facetReflectionQuotientRepresentative P hA hR C e he E g Fa D hD
      Q T hT Droot a ha
  exact ⟨n, σ, hn, hσ⟩

/-- The conditional root comparison gives the existing paired root-datum
predicate, for every proof of splitness of the supplied integral torus. -/
theorem hasApartmentDerivativeRootDatum_of_unramifiedRootComparison
    (hsplit : IsSplitTorus T.torus.toGrp) :
    HasApartmentDerivativeRootDatum P.toValuationBuildingData Q T Droot hsplit Fa := by
  let RD := unramifiedFacetRootDatumOfRootComparison P hA hR C e he E g Fa D hD
    Q T hT hQ Droot hroots
  have : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  have hspecial : IsSplitTorus T.specialFibre.toGrp :=
    IsSplitTorus.baseChange (IntegralModel.residueBaseMap ↥𝒪[F]) hsplit
  exact ⟨relativeRoots (T.specialFibreInclusion ≫ Q.projection),
    (hspecial.finite_relativeRoots _).to_subtype, RD.val, RD.property⟩

end Langlands.BruhatTits.IntegralModels
