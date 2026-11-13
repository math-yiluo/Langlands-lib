import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction

/-! # Twisted-stable chambers through a twisted-fixed point over the maximal unramified
extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedTwistedChamberThroughFixedPointAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Twisted-stable chambers through a twisted-fixed point** (the residual step of
Kaletha–Prasad, Proposition 9.10.1, (4) ⇒ (1), with Proposition 9.10.4, applied to the
twist of the proof of Theorem 10.6.1). Let `K` be the maximal unramified extension of a
nonarchimedean local field `F`, `Γ = Aut(K/F)`, `G` a connected reductive `F`-group, `T` an
`F`-torus of `G` whose scalar extension is a maximal `K`-split torus of `G_K`, and `D`, `C`,
`h6`, `hD` the data of `UnramifiedTwistedChamberStatement`. Let `c : Γ → G(K)` be a crossed
homomorphism that is trivial on the fixing subgroup of a finite subextension of `K/F`. If a
point `y` of the reduced building is fixed by the twisted action `z ↦ c(σ) · σ(z)` of every
`σ ∈ Γ`, then some chamber `Y` is stable under the twisted action of every `σ ∈ Γ` and has a
presentation `Y = g · facet(x₀)`, with `x₀` a point of the apartment on no affine root
hyperplane, such that `y = g · x` for a point `x` of the closure of the facet of `x₀`. -/
def UnramifiedTwistedChamberThroughFixedPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
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
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
        (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          rationalPoints (baseChanged F (inertiaFixedField F) G)),
        (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
        (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
          ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
        ∀ y : (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).ReducedBuilding,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            c σ • (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ y = y) →
          ∃ Y : Set (UnramifiedBuildingDescent.buildingData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT D C h6).ReducedBuilding,
            (UnramifiedBuildingDescent.buildingData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT D C h6).IsChamber Y ∧
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              (fun z => c σ • (UnramifiedBuildingDescent.semilinearData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT C h6 hD).action σ z) '' Y = Y) ∧
            ∃ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
              (x₀ x : (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).Apartment),
              (∀ ψ ∈ (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).affineRoots, ψ x₀ ≠ 0) ∧
              Y = (fun z => g • (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).apartmentMap z) ''
                AffineRootSystem.facet (UnramifiedBuildingDescent.buildingData iT
                  (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                  hiT D C h6).affineRoots x₀ ∧
              x ∈ AffineRootSystem.facetClosure (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).affineRoots x₀ ∧
              g • (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).apartmentMap x = y

end Langlands.Geometry.Building
