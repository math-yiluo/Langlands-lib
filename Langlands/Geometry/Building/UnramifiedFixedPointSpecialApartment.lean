import Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement
import Langlands.Geometry.Building.TorusUnitApartmentFixation

/-! # A special apartment through a prescribed coefficient-fixed point -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The one-point consequence of KP 9.3.8, expressed in a supplied quotient:
a special F-torus has a K-conjugate apartment containing the prescribed point. -/
def UnramifiedFixedPointSpecialApartmentStatement : Prop :=
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
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
          (y : D.ReducedBuilding),
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
          ∃ (S' : CommGroupScheme (Spec (CommRingCat.of F))) (iS' : S'.toGrp ⟶ G)
            (T' : CommGroupScheme (Spec (CommRingCat.of F))) (iT' : T'.toGrp ⟶ G)
            (f' : S' ⟶ T'),
            IsMaximalSplitTorus iS' ∧ IsClosedSubgroup iT' ∧
            CommGroupScheme.groupHom f' ≫ iT' = iS' ∧
            IsMaximalSplitTorus
              (T := (CommGroupScheme.baseChange
                (algebraBaseMap F (inertiaFixedField F))).obj T')
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT') ∧
            ∃ (g : rationalPoints (baseChanged F (inertiaFixedField F) G))
              (e : ((CommGroupScheme.baseChange
                  (algebraBaseMap F (inertiaFixedField F))).obj T).toGrp ≅
                ((CommGroupScheme.baseChange
                  (algebraBaseMap F (inertiaFixedField F))).obj T').toGrp),
              ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) ≫
                  ((baseChanged F (inertiaFixedField F) G).innerIso g).hom =
                e.hom ≫
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT') ∧
              ∃ x : D.Apartment, y = g • D.apartmentMap x

/-- Units of the split subtorus fix a point of the special apartment:
pull their K-points through the conjugacy isomorphism and use full V6. -/
theorem unramifiedFixedPointSplitTorus_of_specialApartment
    (hSpecial : UnramifiedFixedPointSpecialApartmentStatement.{u}) :
    UnramifiedFixedPointSplitTorusStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (baseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD y hy
  obtain ⟨S', iS', T', iT', f', hiS', _, hf', _, g, e, he, x, hxy⟩ :=
    hSpecial F G hG T iT hiT D C h6 hD y hy
  refine ⟨S', iS', hiS', ?_⟩
  intro a ha
  let p : (baseChanged F (inertiaFixedField F) S'.toGrp) ⟶
      ((CommGroupScheme.baseChange
        (baseMap F (inertiaFixedField F))).obj T).toGrp :=
    ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map
      (CommGroupScheme.groupHom f')) ≫ e.inv
  have hfix := torusUnitApartmentFixation (inertiaFixedField F)
    (MaximalUnramified.valuation F) (baseChanged F (inertiaFixedField F) S'.toGrp)
    ((CommGroupScheme.baseChange (baseMap F (inertiaFixedField F))).obj T)
    (baseChanged F (inertiaFixedField F) G)
    ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iT)
    D C h6 p a ha x
  have hp :
      (p ≫ ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iT)) ≫
          ((baseChanged F (inertiaFixedField F) G).innerIso g).hom =
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS') := by
    dsimp only [p]
    rw [Category.assoc, Category.assoc, he, ← Category.assoc e.inv,
      e.inv_hom_id, Category.id_comp, ← Functor.map_comp, hf']
  have hpoint := congrArg (fun f => rationalPoints.map f a) hp
  change rationalPoints.map ((baseChanged F (inertiaFixedField F) G).innerIso g).hom
      (rationalPoints.map
        (p ≫ ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iT)) a) =
    rationalPoints.map
      ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS') a at hpoint
  rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_self] at hpoint
  rw [hxy, ← hpoint]
  have htranslated := congrArg (fun z : D.ReducedBuilding => g • z) hfix
  simpa only [mul_smul, inv_smul_smul] using htranslated

end Langlands.Geometry.Building
