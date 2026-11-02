import Langlands.Global.CurvePlaceAdeleRing
import Langlands.Global.CurvePlaceCompletionCongr

/-! # Presentation transport of actual curve-place restricted products -/

noncomputable section

universe u

open Filter Topology
open scoped RestrictedProduct

namespace Langlands.Global

private theorem eventually_cofinite_equiv {ι κ : Type*} (e : ι ≃ κ) (P : κ → Prop) :
    (∀ᶠ i in cofinite, P (e i)) ↔ ∀ᶠ j in cofinite, P j := by
  constructor
  · intro h
    simpa only [e.apply_symm_apply] using e.symm.injective.tendsto_cofinite.eventually h
  · exact e.injective.tendsto_cofinite.eventually

variable {k F F' : Type u} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F']

private def curvePlacePiEquiv (e : F ≃ₐ[k] F') :
    (∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v) ≃
      (∀ w : AlgebraicCurve.Place k F', curvePlaceCompletion w) :=
  Equiv.piCongr (curvePlaceEquiv e) (fun v => (curvePlaceCompletionCongr e v).toEquiv)

private theorem curvePlacePiEquiv_integral_iff (e : F ≃ₐ[k] F')
    (x : ∀ v : AlgebraicCurve.Place k F, curvePlaceCompletion v) :
    (∀ᶠ v in cofinite, x v ∈ curvePlaceCompletionIntegers v) ↔
      ∀ᶠ w in cofinite, curvePlacePiEquiv e x w ∈ curvePlaceCompletionIntegers w := by
  rw [← eventually_cofinite_equiv (curvePlaceEquiv e)]
  apply Filter.eventually_congr
  apply Filter.Eventually.of_forall
  intro v
  rw [curvePlacePiEquiv, Equiv.piCongr_apply_apply]
  exact (curvePlaceCompletionCongr_mem_integers_iff e v (x v)).symm

private def curvePlaceRestrictedEquiv (e : F ≃ₐ[k] F') :
    CurvePlaceAdeleRing k F ≃ CurvePlaceAdeleRing k F' :=
  (curvePlacePiEquiv e).subtypeEquiv (curvePlacePiEquiv_integral_iff e)

/-- The actual cofinite restricted products are ring equivalent along a field presentation. -/
def curvePlaceAdeleCongr (e : F ≃ₐ[k] F') :
    CurvePlaceAdeleRing k F ≃+* CurvePlaceAdeleRing k F' where
  __ := curvePlaceRestrictedEquiv e
  map_mul' a b := by
    apply RestrictedProduct.ext
    intro w
    obtain ⟨v, rfl⟩ := (curvePlaceEquiv e).surjective w
    change curvePlacePiEquiv e (a * b).val (curvePlaceEquiv e v) =
      curvePlacePiEquiv e a.val (curvePlaceEquiv e v) *
        curvePlacePiEquiv e b.val (curvePlaceEquiv e v)
    simp only [curvePlacePiEquiv, Equiv.piCongr_apply_apply]
    exact (curvePlaceCompletionCongr e v).map_mul (a v) (b v)
  map_add' a b := by
    apply RestrictedProduct.ext
    intro w
    obtain ⟨v, rfl⟩ := (curvePlaceEquiv e).surjective w
    change curvePlacePiEquiv e (a + b).val (curvePlaceEquiv e v) =
      curvePlacePiEquiv e a.val (curvePlaceEquiv e v) +
        curvePlacePiEquiv e b.val (curvePlaceEquiv e v)
    simp only [curvePlacePiEquiv, Equiv.piCongr_apply_apply]
    exact (curvePlaceCompletionCongr e v).map_add (a v) (b v)

theorem curvePlaceAdeleCongr_apply (e : F ≃ₐ[k] F')
    (a : CurvePlaceAdeleRing k F) (v : AlgebraicCurve.Place k F) :
    curvePlaceAdeleCongr e a (curvePlaceEquiv e v) =
      curvePlaceCompletionCongr e v (a v) :=
  Equiv.piCongr_apply_apply _ _ _ _

theorem curvePlaceAdeleCongr_symm_apply (e : F ≃ₐ[k] F')
    (a : CurvePlaceAdeleRing k F') (v : AlgebraicCurve.Place k F) :
    (curvePlaceAdeleCongr e).symm a v =
      (curvePlaceCompletionCongr e v).symm (a (curvePlaceEquiv e v)) := rfl

theorem continuous_curvePlaceAdeleCongr_symm (e : F ≃ₐ[k] F') :
    Continuous (curvePlaceAdeleCongr e).symm := by
  exact RestrictedProduct.mapAlong_continuous
    (fun w : AlgebraicCurve.Place k F' => curvePlaceCompletion w)
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (curvePlaceEquiv e) (curvePlaceEquiv e).injective.tendsto_cofinite
    (fun v => (curvePlaceCompletionCongr e v).symm)
    (Filter.Eventually.of_forall fun v x hx =>
      (curvePlaceCompletionCongr_mem_integers_iff e v _).mp
        (((curvePlaceCompletionCongr e v).apply_symm_apply x).symm ▸ hx))
    (fun v => continuous_curvePlaceCompletionCongr_symm e v)

private def curvePlaceCompletionCast {w w' : AlgebraicCurve.Place k F'}
    (h : w = w') : curvePlaceCompletion w → curvePlaceCompletion w' :=
  fun x => h ▸ x

private theorem continuous_curvePlaceCompletionCast {w w' : AlgebraicCurve.Place k F'}
    (h : w = w') : Continuous (curvePlaceCompletionCast h) := by
  subst w'
  exact continuous_id

private theorem curvePlaceCompletionCast_integral {w w' : AlgebraicCurve.Place k F'}
    (h : w = w') (x : curvePlaceCompletion w)
    (hx : x ∈ curvePlaceCompletionIntegers w) :
    curvePlaceCompletionCast h x ∈ curvePlaceCompletionIntegers w' := by
  subst w'
  exact hx

theorem continuous_curvePlaceAdeleCongr (e : F ≃ₐ[k] F') :
    Continuous (curvePlaceAdeleCongr e) := by
  let E := curvePlaceEquiv e
  let φ := fun w : AlgebraicCurve.Place k F' =>
    curvePlaceCompletionCast (E.apply_symm_apply w) ∘ curvePlaceCompletionCongr e (E.symm w)
  have hφ : ∀ᶠ w in cofinite, Set.MapsTo (φ w)
      (curvePlaceCompletionIntegers (E.symm w)) (curvePlaceCompletionIntegers w) :=
    Filter.Eventually.of_forall fun w x hx =>
      curvePlaceCompletionCast_integral _ _
        ((curvePlaceCompletionCongr_mem_integers_iff e (E.symm w) x).mpr hx)
  have hc := RestrictedProduct.mapAlong_continuous
    (A₁ := fun v : AlgebraicCurve.Place k F => (curvePlaceCompletionIntegers v : Set _))
    (A₂ := fun w : AlgebraicCurve.Place k F' => (curvePlaceCompletionIntegers w : Set _))
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (fun w : AlgebraicCurve.Place k F' => curvePlaceCompletion w)
    E.symm E.symm.injective.tendsto_cofinite φ hφ
    (fun w => (continuous_curvePlaceCompletionCast _).comp
      (continuous_curvePlaceCompletionCongr e (E.symm w)))
  convert hc using 1
  funext a
  apply RestrictedProduct.ext
  intro w
  rfl

/-- The ring comparison preserves the actual restricted-product topologies. -/
def curvePlaceAdeleHomeomorph (e : F ≃ₐ[k] F') :
    CurvePlaceAdeleRing k F ≃ₜ CurvePlaceAdeleRing k F' where
  toEquiv := (curvePlaceAdeleCongr e).toEquiv
  continuous_toFun := continuous_curvePlaceAdeleCongr e
  continuous_invFun := continuous_curvePlaceAdeleCongr_symm e

end Langlands.Global
