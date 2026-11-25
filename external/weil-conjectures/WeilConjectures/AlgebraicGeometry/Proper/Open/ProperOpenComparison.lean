/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
public import WeilConjectures.AlgebraicGeometry.Clopen.ClopenSectionDirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The comparison for a proper morphism fixing an open
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The section of the fibre product induced by `(j₁,id)`. -/
noncomputable def properOpenSection {T₁ T₂ X : Scheme.{u}}
    (f : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ f = j₂) :
    X ⟶ pullback f j₂ :=
  pullback.lift j₁ (𝟙 X) (h.trans (Category.id_comp j₂).symm)

/-- Geometry of the specified section: it is an open and closed immersion, and its
square with `j₁` and the first projection is Cartesian. -/
theorem properOpenSectionGeometry {T₁ T₂ X : Scheme.{u}}
    (f : T₁ ⟶ T₂) [IsProper f] (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (h : j₁ ≫ f = j₂) :
    IsOpenImmersion (properOpenSection f j₁ j₂ h) ∧
      IsClosed (Set.range (properOpenSection f j₁ j₂ h).base) ∧
      IsPullback (𝟙 X) (properOpenSection f j₁ j₂ h) j₁ (pullback.fst f j₂) := by
  have hs_fst : properOpenSection f j₁ j₂ h ≫ pullback.fst f j₂ = j₁ :=
    pullback.lift_fst _ _ _
  have hs_snd : properOpenSection f j₁ j₂ h ≫ pullback.snd f j₂ = 𝟙 X :=
    pullback.lift_snd _ _ _
  have : IsOpenImmersion (properOpenSection f j₁ j₂ h) := by
    have : IsOpenImmersion (properOpenSection f j₁ j₂ h ≫ pullback.fst f j₂) := by
      rw [hs_fst]
      infer_instance
    exact IsOpenImmersion.of_comp (properOpenSection f j₁ j₂ h) (pullback.fst f j₂)
  refine ⟨inferInstance, ?_, ?_⟩
  · have : IsClosedImmersion (properOpenSection f j₁ j₂ h ≫ pullback.snd f j₂) := by
      rw [hs_snd]
      infer_instance
    have : IsClosedImmersion (properOpenSection f j₁ j₂ h) :=
      IsClosedImmersion.of_comp _ (pullback.snd f j₂)
    exact (properOpenSection f j₁ j₂ h).isClosedEmbedding.isClosed_range
  · exact IsPullback.of_horiz_isIso_mono
      ⟨by simpa only [Category.id_comp] using hs_fst.symm⟩

/-- The specified restriction isomorphism `θ = c ∘ Rp_*(e) ∘ r`.
Here `r` is the canonical derived exchange, `e` is extension-by-zero base change
followed by the identity inverse-image identification, and `c` is the uniquely
characterized component-restriction isomorphism of clopenSectionDirectImage. -/
noncomputable def properOpenIdentification (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≅
      K := by
  let s := properOpenSection f j₁ j₂ h
  let geom := properOpenSectionGeometry f j₁ j₂ h
  letI : IsOpenImmersion s := geom.1
  let sq : ChosenCartesianSquare (pullback.fst f j₂) (pullback.snd f j₂) f j₂ :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  letI := isIso_derivedBaseChangeMapPlus_of_openImmersion Λ f j₂
    (pullback.fst f j₂) (pullback.snd f j₂) sq
  let r := (asIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)).app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)
  let e := (extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2).app K ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.mapIso
      ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).app K)
  let c := (clopenSectionDirectImage Λ (pullback.snd f j₂) s geom.2.1
    (pullback.lift_snd j₁ (𝟙 X) _)).choose.app K
  exact r ≪≫ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
    (pullback.snd f j₂)).mapIso e ≪≫ c

/-- The comparison `α = ε ∘ j₂!(θ⁻¹)` in functional composition order:
apply extension by zero to the inverse of the specified `θ`, then the descended counit. -/
noncomputable def properOpenComparison (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj K ⟶
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
    (properOpenIdentification Λ f j₁ j₂ h K).inv ≫
  (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} Λ) j₂).counit.app
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K))

/-- The specified restriction isomorphism `θ = c ∘ Rp_*(e) ∘ r` of
`properOpenIdentification`, for any commutative coefficient ring `Λ`; the finite-coefficient
`properOpenIdentification` is its specialization (`properOpenIdentification_eq_ofCommRing`). -/
noncomputable def properOpenIdentificationOfCommRing (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)) ≅
      K := by
  let s := properOpenSection f j₁ j₂ h
  let geom := properOpenSectionGeometry f j₁ j₂ h
  letI : IsOpenImmersion s := geom.1
  let sq : ChosenCartesianSquare (pullback.fst f j₂) (pullback.snd f j₂) f j₂ :=
    { toCommSq := ⟨pullback.condition⟩
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  letI := isIso_derivedBaseChangeMapPlus_of_openImmersion_of_commRing Λ f j₂
    (pullback.fst f j₂) (pullback.snd f j₂) sq
  let r := (asIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)).app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)
  let e := (extensionZeroBaseChangeDerivedPlusIso Λ geom.2.2).app K ≪≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus.mapIso
      ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).app K)
  let c := (clopenSectionDirectImage_of_commRing Λ (pullback.snd f j₂) s geom.2.1
    (pullback.lift_snd j₁ (𝟙 X) _)).choose.app K
  exact r ≪≫ (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
    (pullback.snd f j₂)).mapIso e ≪≫ c

/-- The comparison `α = ε ∘ j₂!(θ⁻¹)` in functional composition order:
apply extension by zero to the inverse of the specified `θ`, then the descended counit.
The coefficient ring `Λ` is any commutative ring; `properOpenComparison` is its
finite-coefficient case (`properOpenComparison_eq_ofCommRing`). -/
noncomputable def properOpenComparisonOfCommRing (Λ : Type (u + 1)) [CommRing Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.obj K ⟶
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
    (properOpenIdentificationOfCommRing Λ f j₁ j₂ h K).inv ≫
  (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
    (ModuleCat.{u + 1} Λ) j₂).counit.app
      ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K))

/-- At a finite coefficient ring the finite-coefficient identification is the general one. -/
theorem properOpenIdentification_eq_ofCommRing (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenIdentification Λ f j₁ j₂ h K = properOpenIdentificationOfCommRing Λ f j₁ j₂ h K :=
  rfl

/-- At a finite coefficient ring the finite-coefficient comparison is the general one. -/
theorem properOpenComparison_eq_ofCommRing (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ X : Scheme.{u}} (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    properOpenComparison Λ f j₁ j₂ h K = properOpenComparisonOfCommRing Λ f j₁ j₂ h K :=
  rfl

end AlgebraicGeometry.Etale
