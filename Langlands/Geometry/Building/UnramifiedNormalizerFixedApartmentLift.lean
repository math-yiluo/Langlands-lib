import Langlands.Geometry.Building.ScalarTorusUnitsFixApartment
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentStatement
import Langlands.Geometry.Building.UnramifiedFiltrationSharpFixer

/-! # Rational normalizer translates lift to the fixed apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- A rational normalizer transports fixation by the units of its torus. -/
theorem IsFixedByScalarTorusUnits.normalizer_smul
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (valuation : Valuation K (WithZero (Multiplicative ℤ)))
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} (iS : S.toGrp ⟶ G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged k K G)) Y]
    {y : Y} (hy : IsFixedByScalarTorusUnits k K valuation iS y)
    (n : normalizerPoints iS) :
    IsFixedByScalarTorusUnits k K valuation iS
      (rationalExtend k K G (n : rationalPoints G) • y) := by
  have h := hy.conjugate valuation iS iS
    (CommGroupScheme.groupHom (normalizingAut iS n⁻¹).hom)
    (n⁻¹ : normalizerPoints iS).val (isNormalizingPoint_normalizingAut iS n⁻¹)
  simpa only [Subgroup.coe_inv, map_inv, inv_inv] using h

/-- Conditional fixed-apartment lifting for rational normalizer translates. -/
def UnramifiedNormalizerFixedApartmentLiftStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (_hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (_hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (_hf : CommGroupScheme.groupHom f ≫ iT = iS),
  ∀ (_hA : UnramifiedTorusUnitFixedApartmentStatement.{u})
    (_hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (_hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (n : normalizerPoints iS) (x : D.Apartment)
    (_hx : ∀ σ : (inertiaFixedField F) ≃ₐ[F] (inertiaFixedField F),
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val),
    ∃ y : D.Apartment,
      (∀ σ : (inertiaFixedField F) ≃ₐ[F] (inertiaFixedField F),
        RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) ∧
      (D.apartmentMap y : D.ReducedBuilding) =
        (show rationalPoints ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G) from
          rationalExtend F (inertiaFixedField F) G (n : rationalPoints G)) •
            (D.apartmentMap x : D.ReducedBuilding)

section Unramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  [IsAffineHom G.X.hom]
  (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
  (hiS : IsMaximalSplitTorus iS)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)

local notation "Kur" => inertiaFixedField F
local notation "b" => algebraBaseMap F Kur
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged F Kur G
local notation "iT_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

private instance liftExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

include hG hiS hf in
/-- The fixed-apartment theorem puts a rational normalizer translate of a
coefficient-fixed apartment point back in the coefficient-fixed apartment. -/
theorem unramifiedNormalizerFixedApartmentLift
    (hA : UnramifiedTorusUnitFixedApartmentStatement.{u})
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    [Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
    (D : KPApartmentData
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (n : normalizerPoints iS) (x : D.Apartment)
    (hx : ∀ σ : Kur ≃ₐ[F] Kur,
      RootFunctionFamily.galoisAction F Kur T G σ x.val = x.val) :
    ∃ y : D.Apartment,
      (∀ σ : Kur ≃ₐ[F] Kur,
        RootFunctionFamily.galoisAction F Kur T G σ y.val = y.val) ∧
      (D.apartmentMap y : D.ReducedBuilding) =
        (show rationalPoints ((GroupScheme.baseChange b).obj G) from
          rationalExtend F Kur G (n : rationalPoints G)) •
            (D.apartmentMap x : D.ReducedBuilding) := by
  have hD : KPApartmentData.GaloisStable F Kur iT D :=
    (D.galoisStable_iff_equipollent F Kur iT x).2 fun σ => by
      rw [hx σ]
      exact Equipollent.refl _
  have hx' : ∀ σ : Kur ≃ₐ[F] Kur,
      KPApartmentData.galoisAction F Kur iT D hD σ x = x := by
    intro σ
    apply KPApartmentData.Apartment.ext
    exact hx σ
  have hcoeff : ∀ σ : Kur ≃ₐ[F] Kur,
      KPApartmentData.galoisQuotientAction F Kur iT D hD σ
        (rationalExtend F Kur G (n : rationalPoints G) • D.apartmentMap x) =
      rationalExtend F Kur G (n : rationalPoints G) • D.apartmentMap x := by
    intro σ
    rw [KPApartmentData.galoisQuotientAction_smul,
      rationalConjugate_rationalExtend,
      KPApartmentData.galoisQuotientAction_apartmentMap, hx' σ]
  have hunit : IsFixedByUnramifiedTorusUnits F iS (D.apartmentMap x) := by
    intro t ht
    rw [← baseChange_groupHom_comp_of_factorization (k := F) (K := Kur) f hf]
    exact D.map_torusUnits_smul_apartmentMap (MaximalUnramified.valuation F) C hDC
      ((CommGroupScheme.baseChange b).map f) t ht x
  have hunit' : IsFixedByUnramifiedTorusUnits F iS
      (rationalExtend F Kur G (n : rationalPoints G) • D.apartmentMap x) :=
    hunit.normalizer_smul (MaximalUnramified.valuation F) iS n
  exact hA F G hG S iS hiS T iT f hf hiT D C hDC hD _ hcoeff hunit'

end Unramified

/-- The conditional statement is proved by unit fixation and coefficient semilinearity. -/
theorem unramifiedNormalizerFixedApartmentLift_statement :
    UnramifiedNormalizerFixedApartmentLiftStatement.{u} := by
  intro F _ _ _ _ G hG _ S iS hiS T iT f hf hA hiT _ D C hDC n x hx
  exact unramifiedNormalizerFixedApartmentLift F G hG S iS hiS T iT f hf
    hA hiT D C hDC n x hx

end Langlands.Geometry.Building
