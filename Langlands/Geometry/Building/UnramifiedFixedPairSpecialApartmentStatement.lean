import Langlands.Geometry.Building.TorusUnitFixedPoint
import Langlands.Geometry.Building.GaloisApartmentQuotientAction

/-! # Two fixed building points in one centralizing translate of a special apartment over `K` -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- Two coefficient-fixed building points that are fixed by the `K`-units of the maximal
`F`-split torus `S` lie in one translate `g · A` of the supplied apartment, where `g`
centralizes `S_K` and `g⁻¹ σ(g)` normalizes `T_K` for every `σ ∈ Aut(K/F)` (KP
Proposition 9.3.11(1), with corrections, gives a special `F`-torus `T₁ ⊇ S` whose
`K`-apartment contains both points; conjugacy of maximal `K`-split tori in `Z_G(S)_K`
gives `T₁,K = g T_K g⁻¹`). -/
def UnramifiedFixedPairSpecialApartmentStatement : Prop :=
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
          (y₁ y₂ : D.ReducedBuilding),
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₁ = y₁) →
          IsFixedByUnramifiedTorusUnits F iS y₁ →
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₂ = y₂) →
          IsFixedByUnramifiedTorusUnits F iS y₂ →
          ∃ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
            g ∈ centralizerPoints
              (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ∧
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              g⁻¹ * rationalConjugate F (inertiaFixedField F) G σ g ∈
                normalizerPoints
                  (T := (CommGroupScheme.baseChange
                    (algebraBaseMap F (inertiaFixedField F))).obj T)
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) ∧
            (∃ x₁ : D.Apartment, g • D.apartmentMap x₁ = y₁) ∧
            ∃ x₂ : D.Apartment, g • D.apartmentMap x₂ = y₂

end Langlands.Geometry.Building
