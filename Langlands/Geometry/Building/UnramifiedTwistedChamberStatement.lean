import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction

/-! # Chambers stable under a twisted Galois action over the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedTwistedChamberAffineHom {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Twisted-stable chambers** (Kaletha–Prasad, Proposition 9.10.4 with 9.10.1, applied as
in the proof of Theorem 10.6.1). Let `K` be the maximal unramified extension of a
nonarchimedean local field `F`, `Γ = Aut(K/F)`, `G` a connected reductive `F`-group and
`T` an `F`-torus of `G` whose scalar extension `T_K` is a maximal `K`-split torus of `G_K`.
Let `D` be a `Γ`-stable equipollence class of valuations of the root datum of `(G_K, T_K)`
satisfying V 6 for the centralizer datum `C`, so that the reduced building of the building
data `UnramifiedBuildingDescent.buildingData` carries the coefficient action of `Γ`
(`UnramifiedBuildingDescent.semilinearData`). For every crossed homomorphism
`c : Γ → G(K)`, `c (σ * τ) = c σ * σ(c τ)`, that is trivial on the fixing subgroup of a
finite subextension of `K/F`, some chamber `Y` is stable under the twisted action
`y ↦ c(σ) · σ(y)` of every `σ ∈ Γ`. -/
def UnramifiedTwistedChamberStatement : Prop :=
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
        ∃ Y : Set (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).ReducedBuilding,
          (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).IsChamber Y ∧
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (fun y => c σ • (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ y) '' Y = Y

end Langlands.Geometry.Building
