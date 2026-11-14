import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationStatement
import Langlands.Geometry.Building.IntegerValuation

/-! # Centralizers of split units fix split translates in the building over `K` -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- In the building over the maximal unramified extension `K`, an element `g ∈ G(K)`
commuting with all `K`-points of the maximal `F`-split torus `S` and fixing the image
of an apartment point `x` also fixes the image of `v + x` for every `v` in the image
of `V(S_K)` (the corrected independence paragraph before KP Proposition 9.3.13:
the fixed set of `g` contains the `S(K)`-orbit of `x`, whose closed convex hull in
the apartment is `V(S′) + x`). -/
def UnramifiedSplitTranslationFixerStatement : Prop :=
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
        ∀ (g : rationalPoints (baseChanged F (inertiaFixedField F) G)),
          (∀ s : rationalPoints (baseChanged F (inertiaFixedField F) S.toGrp),
            Commute g (rationalPoints.map
              ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS) s)) →
        ∀ x : D.Apartment, g • D.apartmentMap x = D.apartmentMap x →
        ∀ v ∈ splitTranslationDirections F (inertiaFixedField F) iT f,
          g • D.apartmentMap (v +ᵥ x) = D.apartmentMap (v +ᵥ x)

end Langlands.Geometry.Building
