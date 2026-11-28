import Langlands.Correspondence.Laumon.NearbyCycles
import WeilConjectures.TraceFormula.Specialization.NearbyCyclesTateTwist
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.NonFlatPullCube

/-!
# Specialization on the strict charts
-/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [-instance] CategoryTheory.sfbRegularAbMonoidal CategoryTheory.sfbRegularAbSymmetric

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace Langlands.Henniart.Laumon

open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

variable {k : Type u} [Field k]

section Defs

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {A : Type u} [CommRing A] {ι : A →+* endStrictRing k} {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A))

/-- Specialization on the chart, using `ε = j ≫ id` for a complex on `X^nr`. -/
def chartSpecialization
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChart ι f))
      Ab.{u + 1}) (condensedRingObj Λ (strictChart ι f)))) :
    L(((traitNearbyModel ι f).i)^*⟦Λ⟧).obj K ⟶ ((traitNearbyModel ι f).nearbyCycles Λ).obj K :=
  let M := traitNearbyModel ι f
  have h : M.j ≫ 𝟙 (strictChart ι f) = M.ε := Category.comp_id M.j
  M.twistSpecializationMap Λ
    ((leftDerivedUpperStarCompOfEq Λ h).app K ≪≫
      L((M.j)^*⟦Λ⟧).mapIso ((leftDerivedUpperStarId Λ (strictChart ι f)).app K))

/-- Specialization for the pullback of a complex on `X`. -/
def nearbySpecialization
    (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    L(((traitNearbyModel ι f).i)^*⟦Λ⟧).obj (strictChartPullback Λ ι f B) ⟶
      chartNearbyCycles Λ ι f B :=
  chartSpecialization Λ f (strictChartPullback Λ ι f B)

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- The coefficient comparison for the nearby cycles of the chart. -/
def chartNearbyCyclesCoefficientMap
    (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChart ι f))
      Ab.{u + 1}) (condensedRingObj Λ (strictChart ι f)))) :
    (L(Mod.extendScalars (coefficientMap a (strictChartSpecial ι f)))).obj
        (((traitNearbyModel ι f).nearbyCycles Λ).obj K) ⟶
      ((traitNearbyModel ι f).nearbyCycles Λ').obj
        ((L(Mod.extendScalars (coefficientMap a (strictChart ι f)))).obj K) :=
  (derivedUpperStarExtendScalarsIso a (traitNearbyModel ι f).i).hom.app _ ≫
    L(((traitNearbyModel ι f).i)^*⟦Λ'⟧).map
      ((derivedUpperStarExtendScalarsPushHom a (traitNearbyModel ι f).j).app
        ((L(((traitNearbyModel ι f).ε)^*⟦Λ⟧)).obj K)) ≫
    L(((traitNearbyModel ι f).i)^*⟦Λ'⟧).map (R(((traitNearbyModel ι f).j)_*⟦Λ'⟧).map
      ((derivedUpperStarExtendScalarsIso a (traitNearbyModel ι f).ε).hom.app K))

end Defs

/-- Specialization is natural in the complex and compatible with the tensor unit, model
exchanges, the arithmetic action, and derived extension of coefficients. -/
def NearbySpecializationNaturalityStatement : Prop :=
  ∀ (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k],
    (∀ (A : Type u) [CommRing A] (ι : A →+* endStrictRing k) (X : Scheme.{u})
        (f : X ⟶ Spec (.of A))
        (K K' : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChart ι f))
          Ab.{u + 1}) (condensedRingObj Λ (strictChart ι f)))) (g : K ⟶ K'),
      chartSpecialization Λ f K ≫ ((traitNearbyModel ι f).nearbyCycles Λ).map g =
        L(((traitNearbyModel ι f).i)^*⟦Λ⟧).map g ≫ chartSpecialization Λ f K') ∧
    (∀ (A : Type u) [CommRing A] (ι : A →+* endStrictRing k) (X : Scheme.{u})
        (f : X ⟶ Spec (.of A)),
      (traitNearbyModel ι f).unit Λ =
        (leftDerivedUpperStarUnitIso Λ (traitNearbyModel ι f).i).inv ≫
          chartSpecialization Λ f (𝟙_ _)) ∧
    (∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂] (ι₁ : A₁ →+* endStrictRing k)
        (ι₂ : A₂ →+* endStrictRing k) (X₁ X₂ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of A₁))
        (f₂ : X₂ ⟶ Spec (.of A₂)) (a : strictChart ι₁ f₁ ⟶ strictChart ι₂ f₂)
        (a' : strictChartSpecial ι₁ f₁ ⟶ strictChartSpecial ι₂ f₂)
        (φ : (traitNearbyModel ι₁ f₁).Hom (traitNearbyModel ι₂ f₂) a a') (_ : φ.total = a)
        (sq : CommSq (traitNearbyModel ι₁ f₁).i a' a (traitNearbyModel ι₂ f₂).i),
      (∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
          (strictChart ι₂ f₂)) Ab.{u + 1}) (condensedRingObj Λ (strictChart ι₂ f₂))),
        L((a')^*⟦Λ⟧).map (chartSpecialization Λ f₂ K) ≫ (φ.pullbackExchange Λ).app K =
          (pullbackSquareComparison Λ sq).hom.app K ≫
            chartSpecialization Λ f₁ (L((a)^*⟦Λ⟧).obj K)) ∧
      ∀ K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology
          (strictChart ι₁ f₁)) Ab.{u + 1}) (condensedRingObj Λ (strictChart ι₁ f₁))),
        chartSpecialization Λ f₂ (R((a)_*⟦Λ⟧).obj K) ≫ (φ.pushforwardExchange Λ).app K =
          (mateEquiv (derivedUpperStarLowerStarAdjunction Λ a)
              (derivedUpperStarLowerStarAdjunction Λ a')
              (pullbackSquareComparison Λ sq).hom).app K ≫
            R((a')_*⟦Λ⟧).map (chartSpecialization Λ f₁ K)) ∧
    (∀ (A : Type u) [CommRing A] (ι : A →+* endStrictRing k) (X : Scheme.{u})
        (f : X ⟶ Spec (.of A))
        (B : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)))
        (σ : Gal(endGenericClosure k/endField k)) (hσ : (strictRingGalois σ).comp ι = ι),
      L((strictChartSpecialGalois f σ hσ)^*⟦Λ⟧).map (nearbySpecialization Λ f B) ≫
          nearbyCyclesAction Λ f B σ hσ =
        (pullbackSquareComparison Λ (traitNearbyModelGalois f σ hσ).commSq_i).hom.app _ ≫
          L(((traitNearbyModel ι f).i)^*⟦Λ⟧).map
            ((leftDerivedUpperStarCompOfEq Λ (strictChartGalois_projection σ hσ)).inv.app B) ≫
          nearbySpecialization Λ f B) ∧
    ∀ (Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ'] [IsCommMonObj Λ']
      (a : Λ ⟶ Λ') [IsMonHom a] (A : Type u) [CommRing A] (ι : A →+* endStrictRing k)
      (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
      (K : DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (strictChart ι f))
        Ab.{u + 1}) (condensedRingObj Λ (strictChart ι f)))),
      (L(Mod.extendScalars (coefficientMap a (strictChartSpecial ι f)))).map
          (chartSpecialization Λ f K) ≫ chartNearbyCyclesCoefficientMap f a K =
        (derivedUpperStarExtendScalarsIso a (traitNearbyModel ι f).i).hom.app K ≫
          chartSpecialization Λ' f
            ((L(Mod.extendScalars (coefficientMap a (strictChart ι f)))).obj K)

end Langlands.Henniart.Laumon
