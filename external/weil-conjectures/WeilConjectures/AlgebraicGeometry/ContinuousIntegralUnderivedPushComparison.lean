/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison
import WeilConjectures.AlgebraicGeometry.CondensedUnderivedPushforwardContinuity
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # Integral localization commutes with ordinary qcqs pushforward -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ordinary scalar-extension/pushforward comparison is invertible for a qcqs map.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), and Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node)
Proof. Both scalar extensions are the colimits of multiplication-by-ℓ telescopes.
Ordinary qcqs pushforward preserves these filtered colimits. Restrict the specified
mate to integral coefficients and compose with the restriction/pushforward comparison.
The adjunction unit equation identifies its zeroth telescope leg with the pushed
unit. Invertibility of ℓ then identifies every leg. Uniqueness of colimits makes
this restricted comparison invertible; faithful exact restriction reflects it. -/
theorem integralScalarUnderivedPushHom_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    IsIso ((pushHom (integralScalarMap ℓ E) f).app M) := by
  let a := integralScalarMap ℓ E
  let G := lowerStar (integralCoeff ℓ E) f
  let U := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (coefficientMap a Y)
  let LX := Mod.extendScalars (coefficientMap a X)
  let adjX := Mod.extendRestrictAdjunction (coefficientMap a X)
  let adjY := Mod.extendRestrictAdjunction (coefficientMap a Y)
  let κ := comapLowerStarIso a f
  let β := (pushHom a f).app M
  let cX := integralModuleLocalizationCocone ℓ E X M
  let cY := integralModuleLocalizationCocone ℓ E Y (G.obj M)
  let σ := Mod.smulSequenceCompIso G M ℓ
  let d := (Cocone.precompose σ.inv).obj (G.mapCocone cX)
  let g : cY.pt ⟶ d.pt := U.map β ≫ κ.hom.app (LX.obj M)
  let J := (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor
  have : IsFiltered (ULift.{u + 1} ℕ) :=
    IsFiltered.of_equivalence (ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.symm
  have : PreservesColimit (J ⋙ Mod.smulSequence M ℓ) G :=
    lowerStar_preservesFilteredColimit (integralCoeff ℓ E) f _
  have : PreservesColimit (Mod.smulSequence M ℓ) G :=
    Functor.Final.preservesColimit_of_comp J
  obtain ⟨hcX⟩ := integralModuleLocalization_isColimit ℓ E X M
  obtain ⟨hcY⟩ := integralModuleLocalization_isColimit ℓ E Y (G.obj M)
  have hd : IsColimit d :=
    (IsColimit.precomposeHomEquiv σ.symm _).symm (isColimitOfPreserves G hcX)
  have := module_nsmul_isIso ℓ E X (LX.obj M)
  have := module_nsmul_isIso ℓ E Y
    ((Mod.extendScalars (coefficientMap a Y)).obj (G.obj M))
  have hcx : IsIso (ℓ • 𝟙 cX.pt) := by
    change IsIso (ℓ • 𝟙 ((Mod.comap (coefficientMap a X)).obj (LX.obj M)))
    exact mappedScalar_isIso ℓ (Mod.comap (coefficientMap a X)) _
  have : IsIso (ℓ • 𝟙 d.pt) := mappedScalar_isIso ℓ G cX.pt
  have hzero : cY.ι.app 0 ≫ g = d.ι.app 0 := by
    exact localization_comparison_zero ℓ adjX adjY G M g (mate_unit_comap adjX adjY κ M)
  have hg : IsIso g := by
    let z : cY ⟶ d := ⟨g, integralLocalization_coconeLegs ℓ cY d g hzero⟩
    have : IsIso z := IsColimit.hom_isIso hcY hd z
    exact (Cocone.forget _).map_isIso z
  have hβ : IsIso (U.map β) := by
    have heq : U.map β = g ≫ κ.inv.app (LX.obj M) := by
      simp only [g, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id (U.map β)).symm
    rw [heq]
    infer_instance
  have : IsIso β.hom := by
    change IsIso ((Mod.forget _).map (U.map β))
    infer_instance
  have : IsIso ((Mod.forget _).map β) := by
    change IsIso β.hom
    infer_instance
  exact isIso_of_reflects_iso β (Mod.forget _)

end AlgebraicGeometry.ProEtale.CondensedRing
