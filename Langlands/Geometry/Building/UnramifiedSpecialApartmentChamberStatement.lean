import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.GaloisFacetAction
import Langlands.Geometry.Building.AffineReflectionGalleryGeometry

/-! # Ordinary stable chambers in a supplied special apartment -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedSpecialApartmentChamberAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- A special torus contains a maximal base-field split torus and becomes maximal
split over the maximal unramified field. Every compatible stable apartment of
that torus contains an ordinary chamber stable under the coefficient action.
This is the unproved combination of KP 9.3.6, 9.10.4 and 9.10.1. -/
def UnramifiedSpecialApartmentChamberStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
      (f : S ⟶ T),
      CommGroupScheme.groupHom f ≫ iT = iS →
      IsClosedSubgroup iT →
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
          ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D),
            ∃ x : D.Apartment, AffineRootSystem.GalleryGeometry.IsRegular D.affineRoots x ∧
              ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
                KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hD σ ''
                    AffineRootSystem.facet D.affineRoots x =
                  AffineRootSystem.facet D.affineRoots x

end Langlands.Geometry.Building
