import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.GaloisApartmentQuotientAction

/-! # A split-centralizing transporter of special apartments over `K` -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- Let `x₀` be a coefficient-fixed point of the apartment of the special torus `T`,
and let `y` be a coefficient-fixed building point fixed by the `K`-units of the
maximal `F`-split torus `S`. There is `h ∈ G(K)` commuting with `S(K)` and fixing the
image of `x₀` such that `h⁻¹ σ(h)` normalizes `T_K` for every `σ ∈ Aut(K/F)`, and
`y` lies in the `h`-translate of the apartment (KP Proposition 9.3.11(1), with
corrections, gives a special `F`-apartment containing both points; KP Proposition
9.3.12 over `K` with `Ω = {x₀}`, as used in the corrected paragraph before 9.3.13,
supplies `h`). -/
def UnramifiedFixedPointTransporterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
          (x₀ : D.Apartment),
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x₀.val = x₀.val) →
        ∀ y : D.ReducedBuilding,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
          IsFixedByUnramifiedTorusUnits F iS y →
          ∃ h : rationalPoints (baseChanged F (inertiaFixedField F) G),
            (∀ s : rationalPoints (baseChanged F (inertiaFixedField F) S.toGrp),
              Commute h (rationalPoints.map
                ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS) s)) ∧
            h • D.apartmentMap x₀ = D.apartmentMap x₀ ∧
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              h⁻¹ * rationalConjugate F (inertiaFixedField F) G σ h ∈
                normalizerPoints
                  (T := (CommGroupScheme.baseChange
                    (algebraBaseMap F (inertiaFixedField F))).obj T)
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) ∧
            ∃ x₁ : D.Apartment, h • D.apartmentMap x₁ = y

end Langlands.Geometry.Building
