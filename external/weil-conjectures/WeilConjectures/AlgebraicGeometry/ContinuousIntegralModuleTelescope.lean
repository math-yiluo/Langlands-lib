/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # Tensoring the regular localization telescope with a module -/

@[expose] public section

universe u v
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

omit [Fact ℓ.Prime] in
/-- An additive functor preserves invertibility of a natural scalar endomorphism.
Source: functorial preservation of isomorphisms and natural multiples of morphisms.
(auxiliary; not a blueprint node). -/
theorem mappedScalar_isIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (M : A) [IsIso (ℓ • 𝟙 M)] :
    IsIso (ℓ • 𝟙 (F.obj M)) := by
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using F.map_isIso (ℓ • 𝟙 M)

/-- The localization-unit telescope of an integral module is a colimit.
Source: Bhatt--Scholze, Lemma 6.8.2, tensoring the regular localization telescope.
(auxiliary; not a blueprint node).
Proof. Tensor the regular coefficient colimit with M. Balanced tensor preserves
colimits and identifies its vertex with restricted scalar extension of M. The
zeroth leg is the extension unit by the coequalizer formula. Multiplication by ℓ
is invertible at that vertex, so the zeroth-leg equation determines every leg. -/
noncomputable def integralModuleLocalizationCocone (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    Cocone (Mod.smulSequence M ℓ) := by
  have := module_nsmul_isIso ℓ E X
    ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj M)
  exact scalarLocalizationUnitCocone ℓ
    (Mod.extendRestrictAdjunction (coefficientMap (integralScalarMap ℓ E) X)) M

/-- The module localization unit presents scalar extension as its scalar telescope.
Source: Bhatt--Scholze, Lemma 6.8.2.
(auxiliary; not a blueprint node).
Proof. On underlying abelian sheaves, base `Mod.isColimitExtendScalarsCocone`
(`isColimitIntegralExtendScalarsCocone`) presents `E_X ⊗ M` as the colimit of
`M --ℓ--> M --ℓ--> ⋯` with zeroth leg the extension unit. Multiplication by ℓ is
invertible at the vertex, so the zeroth-leg equation identifies every leg with the
unit cocone; the forgetful functor from modules reflects the colimit. -/
theorem integralModuleLocalization_isColimit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    Nonempty (IsColimit (integralModuleLocalizationCocone ℓ E X M)) := by
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let F := Mod.forget (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (integralCoeff ℓ E) X)
  let target := integralModuleLocalizationCocone ℓ E X M
  let α := Mod.smulSequenceCompIso F M ℓ
  let d := (Cocone.precompose α.inv).obj (F.mapCocone target)
  have := module_nsmul_isIso ℓ E X ((Mod.extendScalars φ).obj M)
  have : IsIso (ℓ • 𝟙 d.pt) := mappedScalar_isIso ℓ (Mod.comap φ ⋙ F) _
  let c₀ := Mod.extendScalarsCocone φ (nsmul_coefficientMapInvPow_succ ℓ E X) M
  have hzero : c₀.ι.app 0 ≫ 𝟙 d.pt = d.ι.app 0 := by
    change Mod.extendScalarsCoconeι φ (coefficientMapInvPow ℓ E X) M 0 ≫ 𝟙 _ =
      𝟙 _ ≫ ((Mod.extendUnit φ M).hom ≫ 𝟙 _)
    rw [Category.comp_id, Category.comp_id, Category.id_comp, Mod.extendUnit_hom,
      Mod.extendScalarsCoconeι, coefficientMapInvPow_zero, IsMonHom.one_hom]
    rfl
  have hd : IsColimit d := (isColimitIntegralExtendScalarsCocone ℓ E X M).ofIsoColimit
    (Cocone.ext (Iso.refl _) (integralLocalization_coconeLegs ℓ c₀ d (𝟙 d.pt) hzero))
  exact ⟨isColimitOfReflects F ((IsColimit.precomposeInvEquiv α _) hd)⟩

end AlgebraicGeometry.ProEtale.CondensedRing
