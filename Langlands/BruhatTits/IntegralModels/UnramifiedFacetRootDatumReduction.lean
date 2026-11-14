import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetQuotientRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetRootDatumStatement

/-! # The descended facet root datum from integral opposite factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section SuppliedData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

variable
  (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
  (e : P.ReducedBuilding → C.ReducedBuilding) (hinj : Function.Injective e)
  (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
    e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (g : rationalPoints G) (Fa : Set P.Apartment)
  (D : RelativeComponentModelData ↥𝒪[F] F G)
  (hD : D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer
      (e '' (P.translatedApartmentMap g '' Fa)))
  (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
  (hopp : IntegralOppositeFactorsStatement.{u})
  (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
  (hT : T.IsClosedSplit) (Q : SpecialFibreQuotientData D)
  (hQ : Q.IsReductiveQuotient)

include hinj he hD hA hR hopp hT hQ

/-- The full actual quotient root datum, with its specialized derivative
root-coroot graph, conditional only on integral opposite factors. -/
def unramifiedFacetRootDatumOfIntegralOppositeFactors
    (hne : Fa.Nonempty) (Droot : RelativeRootReflectionData P.i) :
    {RD : RootDatum (relativeRoots (T.specialFibreInclusion ≫ Q.projection))
        (characterLattice T.specialFibre) (cocharacterLattice T.specialFibre) //
      IsRootDatumOf (T.specialFibreInclusion ≫ Q.projection) RD ∧
        Set.range (fun k => (RD.root k, RD.coroot k)) =
          apartmentDerivativeRootCorootGraph P.toValuationBuildingData
            T Droot hT.1 Fa} :=
  unramifiedFacetRootDatumOfRootComparison P hA hR C e he E g Fa D hD Q T hT hQ
    Droot (mem_quotient_roots_iff_inverse_specialization_mem_facetDerivativeRoots
      P C e hinj he E g Fa D hD hA hR hopp T hT Q hQ hne)

/-- The supplied descended data satisfy the complete derivative root datum
predicate, assuming the integral opposite-factor statement. -/
theorem hasApartmentDerivativeRootDatum_of_integralOppositeFactors
    (hne : Fa.Nonempty) (Droot : RelativeRootReflectionData P.i)
    (hsplit : IsSplitTorus T.torus.toGrp) :
    HasApartmentDerivativeRootDatum P.toValuationBuildingData Q T Droot hsplit Fa :=
  hasApartmentDerivativeRootDatum_of_unramifiedRootComparison
    P hA hR C e he E g Fa D hD Q T hT hQ Droot
    (mem_quotient_roots_iff_inverse_specialization_mem_facetDerivativeRoots
      P C e hinj he E g Fa D hD hA hR hopp T hT Q hQ hne) hsplit

end SuppliedData

set_option maxHeartbeats 1000000 in
/-- Integral opposite factors imply the unchanged full descended-facet
root-datum statement at arbitrary universe. -/
theorem unramifiedFacetRootDatum_of_integralOppositeFactors
    (hopp : IntegralOppositeFactorsStatement.{u}) :
    UnramifiedFacetRootDatumStatement.{u} := by
  intro F _ _ _ _ G _ P R T _ _ _ hR hA _ _ C A e a hinj he
    _ _ _ _ _ _ E Fc g Fa hFa hFc D _ hD Q TT Droot hQ hTT hsplit
  have hD' : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        (e '' (P.translatedApartmentMap g '' Fa)) := by
    simpa only [hFc] using hD
  have hne : Fa.Nonempty := by
    obtain ⟨y, hy⟩ := hFa
    exact ⟨y, hy ▸ AffineRootSystem.mem_facet_self P.affineRoots y⟩
  exact hasApartmentDerivativeRootDatum_of_integralOppositeFactors
    P C e hinj he E g Fa D hD' hA hR hopp TT hTT.1 Q hQ hne Droot hsplit

end Langlands.BruhatTits.IntegralModels
