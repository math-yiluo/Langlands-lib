import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction

/-! # Chambers through a twisted-fixed point stable under one topological generator -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedTwistedGeneratorChamberAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Chambers through a twisted-fixed point stable under one topological generator**
(the residual-field core of Kaletha–Prasad, Proposition 9.10.1, (4) ⇒ (1), with
Proposition 9.10.4, applied to the twist of the proof of Theorem 10.6.1, for a single
Frobenius element). Take the data of `UnramifiedTwistedChamberThroughFixedPointStatement`:
`K` the maximal unramified extension of a nonarchimedean local field `F`, `Γ = Aut(K/F)`, the
building over `K` of the supplied `Γ`-stable apartment class `D`, its coefficient action, and a
crossed homomorphism `c : Γ → G(K)` trivial on the fixing subgroup of a finite subextension.
If a point `y` of the reduced building is fixed by the twisted action `z ↦ c(σ) · σ(z)` of every
`σ ∈ Γ`, then there is `φ ∈ Γ` whose integer powers meet every coset of the fixing subgroup of
every finite subextension of `K/F` (a topological generator, such as a Frobenius element), and a
chamber `Y = g · facet(x₀)` with `x₀` on no affine root hyperplane, stable under the twisted
action of `φ`, such that `y = g · x` for a point `x` of the closure of the facet of `x₀`. -/
def UnramifiedTwistedGeneratorChamberStatement : Prop :=
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
          ∃ φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (∀ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E →
              ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
                ∃ n : ℤ, σ⁻¹ * φ ^ n ∈ E.fixingSubgroup) ∧
            ∃ Y : Set (UnramifiedBuildingDescent.buildingData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT D C h6).ReducedBuilding,
              (fun z => c φ • (UnramifiedBuildingDescent.semilinearData iT
                (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                hiT C h6 hD).action φ z) '' Y = Y ∧
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
