import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Building.TorusUnitApartmentFixation
import Langlands.Geometry.Building.RootBuildingGaloisFieldExtension

/-! # Fixed image and torus units for the unramified descent map -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.UnramifiedBuildingDescent

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}

private instance fixedImageExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

variable (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  [Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
  (B : ValuationBuildingData G)
  (fixed : D.Apartment → Prop) (φ : D.Apartment → RootFunctionFamily B.S G)
  (hcar : ∀ ψ : RootFunctionFamily B.S G,
    ψ ∈ B.apartment.carrier ↔ ∃ x, fixed x ∧ ψ = φ x)
  (hinj : ∀ x y, fixed x → fixed y → φ x = φ y → x = y)
  (hnorm : ∀ (n : normalizerPoints B.i) (x : D.Apartment), fixed x →
    ∃ y, fixed y ∧
      D.apartmentMap y = rationalExtend F (inertiaFixedField F) G
        (n : rationalPoints G) • D.apartmentMap x ∧ φ y = n • φ x)
  (hfilt : ∀ (x : D.Apartment) (w : B.Apartment), w.val = φ x →
    ∀ a : relativeRoots B.i,
      B.filtration w a 0 ≤ (D.sharpFixer {x}).comap
        (rationalExtend F (inertiaFixedField F) G))
  (hfixed : ∀ x : D.Apartment, fixed x →
    ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)

include hfixed in
/-- The quotient descent map lands in the fixed locus of the actual coefficient action. -/
theorem descentMap_fixed (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (z : B.ReducedBuilding) :
    (semilinearData iT hGK hiT C h6 hD).action σ
        (descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z) =
      descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z := by
  obtain ⟨g, w, rfl⟩ := B.exists_smul_apartmentMap z
  rw [descentMap_smul, descentMap_apartment, semilinearData_action_apply,
    KPApartmentData.galoisQuotientAction_smul, rationalConjugate_rationalExtend,
    KPApartmentData.galoisQuotientAction_apartmentMap]
  congr 1
  congr 1
  apply KPApartmentData.Apartment.ext
  exact hfixed _ (descentPoint_fixed B fixed φ hcar w) σ

/-- The existing descent map with codomain restricted to coefficient-fixed building points. -/
def fixedDescentMap : B.ReducedBuilding →
    {y : (buildingData iT hGK hiT D C h6).ReducedBuilding //
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        (semilinearData iT hGK hiT C h6 hD).action σ y = y} :=
  fun z => ⟨descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z,
    fun σ => descentMap_fixed hGK hiT C h6 hD B fixed φ hcar hinj hnorm hfilt hfixed σ z⟩

@[simp]
theorem fixedDescentMap_val (z : B.ReducedBuilding) :
    (fixedDescentMap hGK hiT C h6 hD B fixed φ hcar hinj hnorm hfilt hfixed z).val =
      descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt z := rfl

/-- Bounded scalar-extended points of the lower torus fix every descended apartment point. -/
theorem descentMap_torusUnits (f : B.S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = B.i)
    (s : rationalPoints (baseChanged F (inertiaFixedField F) B.S.toGrp))
    (hs : s ∈ characterValuationKernel (MaximalUnramified.valuation F)
      (baseChanged F (inertiaFixedField F) B.S.toGrp)) (w : B.Apartment) :
    rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map B.i) s •
      descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt (B.apartmentMap w) =
      descentMap hGK hiT C h6 B fixed φ hcar hinj hnorm hfilt (B.apartmentMap w) := by
  rw [descentMap_apartment]
  have h := isFixedByScalarTorusUnits_apartmentMap F (inertiaFixedField F)
    (MaximalUnramified.valuation F) iT (CommGroupScheme.groupHom f) D C h6
    (descentPoint B fixed φ hcar w)
  rw [hf] at h
  exact h s hs

end Langlands.Geometry.Building.UnramifiedBuildingDescent
