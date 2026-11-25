/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsSequentialColimit
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Exactness of integral scalar localization

For a normed extension `E` of `ℚ_ℓ` with closed unit ball `𝒪_E`, the condensed ring `E̲` is the
sequential colimit `colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)` along the maps `ℓ⁻ᵏ φ`
(`isColimitIntegralCoeffSmulSequenceCocone`), and so is `E_X = p_X^* E̲` over `𝒪_{E,X}`
(`isColimitCoefficientMapSmulSequenceCocone`). The base `Mod.smulSequence` API then gives
`E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)` (`isColimitIntegralExtendScalarsCocone`) and the
exactness of `E_X ⊗_{𝒪_{E,X}} -` (`integralScalarExtension_exact`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

private lemma ell_ne_zero : (ℓ : E) ≠ 0 := by
  have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h

/-- The map `c_k = ℓ⁻ᵏ φ : 𝒪̲_E ⟶ E̲`, where `φ` is the inclusion `integralScalarMap`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def integralScalarMapInvPow (k : ℕ) :
    integralCoeff.{u} ℓ E ⟶ Profinite.continuousMapRingObj E :=
  integralScalarMap ℓ E ≫ Profinite.continuousMapRingObjMulLeft E ((ℓ : E)⁻¹ ^ k)

lemma integralScalarMapInvPow_zero :
    integralScalarMapInvPow.{u} ℓ E 0 = integralScalarMap ℓ E := by
  rw [integralScalarMapInvPow, pow_zero, Profinite.continuousMapRingObjMulLeft_one,
    Category.comp_id]

lemma nsmul_integralScalarMapInvPow_succ (k : ℕ) :
    ℓ • integralScalarMapInvPow.{u} ℓ E (k + 1) = integralScalarMapInvPow ℓ E k := by
  rw [integralScalarMapInvPow, integralScalarMapInvPow, ← Preadditive.comp_nsmul,
    Profinite.nsmul_continuousMapRingObjMulLeft, pow_succ', ← _root_.mul_assoc,
    mul_inv_cancel₀ (ell_ne_zero ℓ E), _root_.one_mul]

/-- **`E̲ = colim(𝒪̲_E --ℓ--> 𝒪̲_E --ℓ--> ⋯)`** for the closed unit ball `𝒪_E` of a normed
extension `E` of `ℚ_ℓ`: the maps `ℓ⁻ᵏ φ` exhibit `E̲` as the sequential colimit of the
multiplications by `ℓ` on `𝒪̲_E`. This is base
`Profinite.isColimitPadicIntegersRingObjSmulSequenceCocone` for a general normed `E`. Sectionwise,
every continuous map from a profinite set to `E` has a common denominator `ℓⁿ`
(`continuousIntegralFunctions_isLocalization`), and the maps `ℓ⁻ᵏ φ` are injective.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def isColimitIntegralCoeffSmulSequenceCocone :
    IsColimit (Mod.smulSequenceCocone ℓ (integralScalarMapInvPow.{u} ℓ E)
      (nsmul_integralScalarMapInvPow_succ ℓ E)) := by
  have hℓ : (ℓ : E) ≠ 0 := by
    have h : (ℓ : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne h
  have := preservesSmallestFilteredColimits_of_preservesFilteredColimits (forget Ab.{u + 1})
  have : ReflectsColimitsOfShape ℕ (forget Ab.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (sheafToPresheaf _ _) ?_
  refine evaluationJointlyReflectsColimits _ fun S ↦
    isColimitOfReflects (forget Ab.{u + 1}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro x
    obtain ⟨x⟩ := x
    let φ := (continuousIntegers ℓ E).subtype.compLeftContinuous S.unop continuous_subtype_val
    let := φ.toAlgebra
    have hloc := continuousIntegralFunctions_isLocalization ℓ E S.unop
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj
      (ContinuousMap.const S.unop (ℓ : continuousIntegers ℓ E)) x
    refine ⟨n, ULift.up a, ULift.ext (ContinuousMap.ext fun s ↦ ?_)⟩
    have ha' := congrArg (fun f : C(S.unop, E) ↦ f s) ha
    change x s * (ℓ : E) ^ n = (a s : E) at ha'
    have key : (ℓ : E)⁻¹ ^ n * (a s : E) = x s := by
      rw [← ha', inv_pow, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero n hℓ), mul_comm]
    exact key.symm
  · intro k x y h
    refine ⟨k, 𝟙 k, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    have hk : (ℓ : E)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero hℓ)
    have h' (s : S.unop) :
        (ℓ : E)⁻¹ ^ k * (x s : E) = (ℓ : E)⁻¹ ^ k * (y s : E) :=
      congrArg (fun z : ULift.{u + 1} C(S.unop, E) ↦ z.down s) h
    obtain rfl : x = y := ContinuousMap.ext fun s ↦ Subtype.ext (mul_left_cancel₀ hk (h' s))
    rfl

/-- The inverse image `p_X^*` from the point is additive, being a left adjoint (as the base
instance `AlgebraicGeometry.ProEtale.additive_upperStarFromPoint`, which lives outside this
import closure). -/
private lemma upperStarFromPoint_additive (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)

/-- The map `p_X^*(ℓ⁻ᵏ φ) : 𝒪_{E,X} ⟶ E_X` on `X_proét`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable abbrev coefficientMapInvPow (X : Scheme.{u}) (k : ℕ) :
    condensedRingObj (integralCoeff.{u} ℓ E) X ⟶
      condensedRingObj (Profinite.continuousMapRingObj E) X :=
  coefficientMap (integralScalarMapInvPow ℓ E k) X

lemma coefficientMapInvPow_zero (X : Scheme.{u}) :
    coefficientMapInvPow ℓ E X 0 = coefficientMap (integralScalarMap ℓ E) X :=
  congrArg (upperStarFromPoint X).map (integralScalarMapInvPow_zero.{u} ℓ E)

/-- `ℓ • p_X^*(ℓ⁻ᵏ⁻¹ φ) = p_X^*(ℓ⁻ᵏ φ)`. -/
lemma nsmul_coefficientMapInvPow_succ (X : Scheme.{u}) (k : ℕ) :
    ℓ • coefficientMapInvPow ℓ E X (k + 1) = coefficientMapInvPow ℓ E X k := by
  have := upperStarFromPoint_additive X
  rw [← (upperStarFromPoint X).map_nsmul, nsmul_integralScalarMapInvPow_succ]

/-- **`E_X = colim(𝒪_{E,X} --ℓ--> 𝒪_{E,X} --ℓ--> ⋯)`**, along the maps `p_X^*(ℓ⁻ᵏ φ)`: the
image of `isColimitIntegralCoeffSmulSequenceCocone` under the additive left adjoint `p_X^*`
(`Mod.isColimitSmulSequenceCoconeMap`). This is base
`isColimitPadicIntegersToPadicSubfieldSmulSequenceCocone` for a general normed `E`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def isColimitCoefficientMapSmulSequenceCocone (X : Scheme.{u}) :
    IsColimit (Mod.smulSequenceCocone ℓ (coefficientMapInvPow ℓ E X)
      (nsmul_coefficientMapInvPow_succ ℓ E X)) := by
  have adj : upperStarFromPoint X ⊣ _ := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  have : (upperStarFromPoint X).IsLeftAdjoint := adj.isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (upperStarFromPoint X)
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    adj.leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  have := Functor.additive_of_preservesBinaryBiproducts (upperStarFromPoint X)
  exact Mod.isColimitSmulSequenceCoconeMap (upperStarFromPoint X) _
    (isColimitIntegralCoeffSmulSequenceCocone ℓ E)

/-- **`E_X ⊗_{𝒪_{E,X}} M = colim(M --ℓ--> M --ℓ--> ⋯)`** for every `𝒪_{E,X}`-module `M`
(base `Mod.isColimitExtendScalarsCocone`). This is base
`isColimitPadicIntegersExtendScalarsCocone` for a general normed `E`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
noncomputable def isColimitIntegralExtendScalarsCocone (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) :
    IsColimit (Mod.extendScalarsCocone (coefficientMap (integralScalarMap ℓ E) X)
      (nsmul_coefficientMapInvPow_succ ℓ E X) M) :=
  Mod.isColimitExtendScalarsCocone _ (isColimitCoefficientMapSmulSequenceCocone ℓ E X)
    (Mod.linear_of_isColimit _ (isColimitCoefficientMapSmulSequenceCocone ℓ E X)
      (coefficientMapInvPow_zero ℓ E X)) M

/-- Integral-to-E scalar extension is exact. `E_X = p_X^* E̲` is the sequential colimit of the
multiplications by `ℓ` on `𝒪_{E,X} = p_X^* 𝒪̲_E` (`isColimitCoefficientMapSmulSequenceCocone`),
so base `Mod.preservesFiniteLimits_extendScalars_of_isColimit` applies. This is the proof of base
`preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield` for a general normed `E`.
Source: Bhatt--Scholze, Lemma 6.8.2
(auxiliary; not a blueprint node). -/
@[instance] theorem integralScalarExtension_exact (X : Scheme.{u}) :
    PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)) := by
  have := AB5OfSize_of_univLE.{0, 0} (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  exact Mod.preservesFiniteLimits_extendScalars_of_isColimit _
    (isColimitCoefficientMapSmulSequenceCocone ℓ E X) (coefficientMapInvPow_zero ℓ E X)

end AlgebraicGeometry.ProEtale.CondensedRing
