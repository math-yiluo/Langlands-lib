import Langlands.Geometry.Building.ApartmentGaloisAction
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.Geometry.Building.ValuationBuildingData

/-! # Special tori and Galois-fixed apartment points over the maximal unramified extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedSpecialApartmentAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Special tori exist** (KP Proposition 9.3.4). Let `K` be the maximal unramified
extension of a nonarchimedean local field `F`. Every maximal `F`-split torus `S` of a
connected reductive `F`-group `G` lies in a closed `F`-subgroup `T` whose scalar extension
`T_K` is a maximal `K`-split torus of `G_K`. -/
def SpecialTorusExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
      IsMaximalSplitTorus iS →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
        CommGroupScheme.groupHom f ≫ iT = iS ∧ IsClosedSubgroup iT ∧
        IsMaximalSplitTorus
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)

/-- **Galois-fixed points of a stable special apartment** (KP §9.2.1). Let `K` be the
maximal unramified extension of a nonarchimedean local field `F`, with its integer-valued
valuation, and let `T` be an `F`-torus of a connected reductive `F`-group `G` whose scalar
extension `T_K` is a maximal `K`-split torus of `G_K`. Every equipollence class of
valuations of the root datum of `(G_K, T_K)` that is stable under the coefficient action of
`Aut(K/F)` has a point fixed by every element of `Aut(K/F)`. -/
def UnramifiedGaloisFixedApartmentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hi : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i)),
      haveI := mono_of_isMaximalSplitTorus hi
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map i).hom.hom.left :=
        mono_of_isMaximalSplitTorus hi
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map i)
          (IntegerValuation.order (MaximalUnramified.valuation F))),
        KPApartmentData.GaloisStable F (inertiaFixedField F) i D →
        ∃ x : D.Apartment, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val

/-- The two unramified-descent inputs of this module: KP Proposition 9.3.4 and the
Galois-fixed point of KP §9.2.1. -/
def UnramifiedSpecialApartmentStatement : Prop :=
  SpecialTorusExistenceStatement.{u} ∧ UnramifiedGaloisFixedApartmentStatement.{u}

end Langlands.Geometry.Building
