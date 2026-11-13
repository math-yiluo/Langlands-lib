import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.Geometry.Building.KPBuilding

/-! # Levi sharp transport from membership in an unramified apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedLeviSharpApartmentTransportAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Levi sharp transport from chart membership.** In the maximal-unramified setting,
let `n` normalize the scalar extension of the maximal base-field split torus `S`. If `n`
carries an apartment point to another point of the same apartment in the sharp-fixer
quotient, then multiplication on the right by an element of the depth-zero root groups
of the Levi `Z_G(S)_K` makes `n` normalize the apartment torus. This is a derived
consequence of Levi apartment transitivity, KP Propositions 7.6.4(2), 7.7.5(4) and §9.7.4. -/
def UnramifiedLeviSharpApartmentTransportStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
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
        ∀ (n : normalizerPoints
            (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS))
          (x : D.Apartment),
          (∃ y : D.Apartment, D.apartmentMap y =
            (n : rationalPoints ((GroupScheme.baseChange
              (algebraBaseMap F (inertiaFixedField F))).obj G)) • D.apartmentMap x) →
          ∃ h : rationalPoints ((GroupScheme.baseChange
              (algebraBaseMap F (inertiaFixedField F))).obj G),
            h ∈ centralizerPoints
              (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ∧
            h ∈ (⨆ (χ : characterLattice
                ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
              (_ : χ ∈ relativeRoots
                (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
              (_ : (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫
                χ = 0), D.filtration x χ 0) ∧
            (n : rationalPoints ((GroupScheme.baseChange
                (algebraBaseMap F (inertiaFixedField F))).obj G)) * h ∈
              normalizerPoints
                (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)

end Langlands.Geometry.Building
