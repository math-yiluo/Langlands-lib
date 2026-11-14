import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredRootRestriction
import Langlands.BruhatTits.IntegralModels.ReductiveQuotientExistence
import Langlands.Geometry.Building.UnramifiedIncidentRootChamber

/-! # Ordinary stable chambers from recovered apartment models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2500

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels
namespace RecoveredApartmentFixerModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  {Ω : Set D.Apartment}
  (M : RecoveredApartmentFixerModels D Ω)
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {f : S ⟶ T}
  (hiS : IsMaximalSplitTorus iS)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))

private instance recoveredChamberExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable
  (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
  (p : D.Apartment)
  (hN : M.upper.neutral.integralPoints =
    E.zeroPoints ⊓ D.pointwiseFixer (D.apartmentMap '' {p}))
  (hpositive : UnramifiedRootPositiveReductionStatement.{u})

include M C hDC hiS hf hG hiT E hN hpositive in
/-- Actual recovered models and the retained neutral-fixer and positive-reduction
inputs supply the incident fixed directions, without a supplied quotient. -/
theorem hasIncidentGaloisDirections_of_recoveredModels :
    KPApartmentData.HasIncidentGaloisDirections F (inertiaFixedField F) iT D p := by
  obtain ⟨Q, hQ⟩ := SpecialFibreQuotientData.exists_isReductiveQuotient M.lower
  apply KPApartmentData.hasIncidentGaloisDirections_of_root_comp_ne_zero
    F (inertiaFixedField F) iT hiS.isSplitSubtorus.1 f D p
  rintro a ⟨ψ, hψ, hp, hlin⟩
  exact M.incident_root_restrict_ne_zero C hDC hiS hf hG hiT
    Q hQ E p hN hpositive a hψ hp hlin

variable
  (hstable : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
  (hp : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
    KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hstable σ p = p)

include M C hDC hiS hf hG hiT E p hN hpositive hp in
/-- The same supplied apartment contains an ordinary regular point whose whole
sign facet is coefficient-stable, under the explicit recovered-model inputs. -/
theorem exists_regular_galois_stable_facet_of_recoveredModels :
    ∃ x : D.Apartment, AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x ∧
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hstable σ ''
            AffineRootSystem.facet D.affineRoots x =
          AffineRootSystem.facet D.affineRoots x := by
  exact KPApartmentData.exists_regular_galois_stable_facet_of_directions
    F (inertiaFixedField F) iT D
    (hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)) hiT C hDC
    hstable p hp
    (M.hasIncidentGaloisDirections_of_recoveredModels C hDC hiS hf hG hiT E p hN hpositive)

/-- Choose an ordinary chamber point from actual recovered models and the
explicit neutral-fixer, positive-reduction and fixed-point inputs. -/
def recoveredApartmentChamberPoint :
    {x : D.Apartment // AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x ∧
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hstable σ ''
            AffineRootSystem.facet D.affineRoots x =
          AffineRootSystem.facet D.affineRoots x} :=
  ⟨(M.exists_regular_galois_stable_facet_of_recoveredModels
      C hDC hiS hf hG hiT E p hN hpositive hstable hp).choose,
    (M.exists_regular_galois_stable_facet_of_recoveredModels
      C hDC hiS hf hG hiT E p hN hpositive hstable hp).choose_spec⟩

end RecoveredApartmentFixerModels
end Langlands.BruhatTits.IntegralModels
