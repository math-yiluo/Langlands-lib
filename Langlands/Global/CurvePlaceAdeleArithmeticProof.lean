import Langlands.Global.CurvePlaceAdeleArithmeticStatement
import Langlands.Global.CurvePlaceExtension

/-! # Faithfulness and coherence of actual curve-place adelic maps -/

noncomputable section

universe u

open IsDedekindDomain
open scoped RestrictedProduct

namespace Langlands.Global

section Level

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

theorem injective_curvePlaceAdeleLevelDiagonal
    [Nonempty (AlgebraicCurve.Place k F)]
    (S : Finset (AlgebraicCurve.Place k F)) :
    Function.Injective (curvePlaceAdeleLevelDiagonal k F S) := by
  let v : AlgebraicCurve.Place k F := Classical.choice inferInstance
  intro a b hab
  apply Subtype.ext
  apply (algebraMap F (curvePlaceCompletion v)).injective
  exact congrArg (fun z : curvePlaceAdeleLevel k F S =>
    (z : CurvePlaceAdeleRing k F) v) hab

theorem injective_curvePlaceAdeleLevelDiagonal_of_functionField
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] (S : Finset (AlgebraicCurve.Place k F)) :
    Function.Injective (curvePlaceAdeleLevelDiagonal k F S) := by
  let := curvePlace_nonempty k F
  exact injective_curvePlaceAdeleLevelDiagonal k F S

theorem injective_curvePlaceAdeleDiagonal
    [PerfectField k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] :
    Function.Injective (curvePlaceAdeleDiagonal k F) := by
  intro x y hxy
  apply (algebraMap F (curvePlaceCompletion (curvePlaceReference k F))).injective
  exact congrArg (fun a : CurvePlaceAdeleRing k F => a (curvePlaceReference k F)) hxy

end Level

section Presentation

variable {k F F' F'' : Type u} [Field k] [Field F] [Field F'] [Field F'']
  [Algebra k F] [Algebra k F'] [Algebra k F'']

theorem curvePlaceEquiv_refl_apply (v : AlgebraicCurve.Place k F) :
    curvePlaceEquiv (AlgEquiv.refl : F ≃ₐ[k] F) v = v := by
  rfl

theorem curvePlaceEquiv_trans_apply (e : F ≃ₐ[k] F') (f : F' ≃ₐ[k] F'')
    (v : AlgebraicCurve.Place k F) :
    curvePlaceEquiv (e.trans f) v = curvePlaceEquiv f (curvePlaceEquiv e v) := by
  rfl

theorem curvePlaceCompletionCongr_refl (v : AlgebraicCurve.Place k F) :
    curvePlaceCompletionCongr (AlgEquiv.refl : F ≃ₐ[k] F) v =
      RingEquiv.refl (curvePlaceCompletion v) := by
  apply DFunLike.coe_injective
  apply (HeightOneSpectrum.denseRange_algebraMap F v.heightOneSpectrum).equalizer
    (continuous_curvePlaceCompletionCongr _ _) continuous_id
  funext x
  exact curvePlaceCompletionCongr_algebraMap (AlgEquiv.refl : F ≃ₐ[k] F) v x

theorem curvePlaceCompletionCongr_trans (e : F ≃ₐ[k] F') (f : F' ≃ₐ[k] F'')
    (v : AlgebraicCurve.Place k F) :
    curvePlaceCompletionCongr (e.trans f) v =
      (curvePlaceCompletionCongr e v).trans
        (curvePlaceCompletionCongr f (curvePlaceEquiv e v)) := by
  apply DFunLike.coe_injective
  apply (HeightOneSpectrum.denseRange_algebraMap F v.heightOneSpectrum).equalizer
    (continuous_curvePlaceCompletionCongr (e.trans f) v)
    ((continuous_curvePlaceCompletionCongr f (curvePlaceEquiv e v)).comp
      (continuous_curvePlaceCompletionCongr e v))
  funext x
  change curvePlaceCompletionCongr (e.trans f) v
      (algebraMap F (curvePlaceCompletion v) x) =
    curvePlaceCompletionCongr f (curvePlaceEquiv e v)
      (curvePlaceCompletionCongr e v (algebraMap F (curvePlaceCompletion v) x))
  simp only [curvePlaceCompletionCongr_algebraMap, AlgEquiv.trans_apply]
  rfl

theorem curvePlaceAdeleCongr_refl :
    curvePlaceAdeleCongr (AlgEquiv.refl : F ≃ₐ[k] F) =
      RingEquiv.refl (CurvePlaceAdeleRing k F) := by
  apply RingEquiv.ext
  intro a
  apply RestrictedProduct.ext
  intro v
  change curvePlaceAdeleCongr (AlgEquiv.refl : F ≃ₐ[k] F) a
    (curvePlaceEquiv (AlgEquiv.refl : F ≃ₐ[k] F) v) = a v
  rw [curvePlaceAdeleCongr_apply, curvePlaceCompletionCongr_refl]
  rfl

theorem curvePlaceAdeleCongr_trans (e : F ≃ₐ[k] F') (f : F' ≃ₐ[k] F'') :
    curvePlaceAdeleCongr (e.trans f) =
      (curvePlaceAdeleCongr e).trans (curvePlaceAdeleCongr f) := by
  apply RingEquiv.ext
  intro a
  apply RestrictedProduct.ext
  intro w
  obtain ⟨v, rfl⟩ := (curvePlaceEquiv (e.trans f)).surjective w
  change curvePlaceAdeleCongr (e.trans f) a (curvePlaceEquiv (e.trans f) v) =
    curvePlaceAdeleCongr f (curvePlaceAdeleCongr e a)
      (curvePlaceEquiv f (curvePlaceEquiv e v))
  rw [curvePlaceAdeleCongr_apply, curvePlaceAdeleCongr_apply,
    curvePlaceAdeleCongr_apply, curvePlaceCompletionCongr_trans]
  rfl

end Presentation

theorem curvePlaceAdeleArithmetic : CurvePlaceAdeleArithmeticStatement.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k F _ _ _ _ S
    exact injective_curvePlaceAdeleLevelDiagonal k F S
  · intro k F _ _ _ _ _ _ _
    exact injective_curvePlaceAdeleDiagonal k F
  · intro k F _ _ _
    exact curvePlaceAdeleCongr_refl
  · intro k F F' F'' _ _ _ _ _ _ _ e f
    exact curvePlaceAdeleCongr_trans e f

end Langlands.Global
