import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Analysis.MixedParameterDerivatives
import Langlands.Global.RankinSelberg.RealPrincipalSeriesCoefficientGrowth
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Smoothness of coefficients of compact-derivative-bounded forms -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Filter Set
open scoped Topology Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "D" => rightDerivative (matrixModel ℝ (r + 1))
local notation "word" => RealLocalWhittaker.iteratedRightDerivative r

private def unitDomain : Set Mat := {x | IsUnit x}

local notation "U" => unitDomain (r := r)

private theorem isOpen_unitDomain : IsOpen (U : Set Mat) :=
  isOpen_setOf_isUnit_matrix

private def jointDirection (X : Mat) (H : Mat × Mat → ℂ) : Mat × Mat → ℂ :=
  fun p => fderiv ℝ H p (0, p.2 * X)

private def jointWord (Xs : List Mat) (H : Mat × Mat → ℂ) : Mat × Mat → ℂ :=
  Xs.foldr jointDirection H

private theorem contDiffOn_jointDirection (X : Mat) {H : Mat × Mat → ℂ}
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ U)) : ContDiffOn ℝ ∞ (jointDirection X H) (U ×ˢ U) :=
  (hH.fderiv_of_isOpen (isOpen_unitDomain.prod isOpen_unitDomain) (by simp)).clm_apply
    (contDiffOn_const.prodMk (contDiffOn_snd.mul contDiffOn_const))

private theorem contDiffOn_jointWord (Xs : List Mat) {H : Mat × Mat → ℂ}
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ U)) : ContDiffOn ℝ ∞ (jointWord Xs H) (U ×ˢ U) := by
  induction Xs with
  | nil => exact hH
  | cons X Xs ih => exact contDiffOn_jointDirection X ih

private def jointTranslate (f : G → ℂ) : Mat × Mat → ℂ :=
  fun p => unitsExtension f (p.2 * p.1)

private theorem contDiffOn_jointTranslate {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ f) :
    ContDiffOn ℝ ∞ (jointTranslate f) (U ×ˢ U) :=
  (contDiffOn_unitsExtension hf).comp (contDiffOn_snd.mul contDiffOn_fst)
    (fun _ hp => hp.2.mul hp.1)

private theorem jointWord_translate_value {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ f)
    (Xs : List Mat) (g k : G) :
    jointWord Xs (jointTranslate f) (g.val, k.val) = word Xs (fun h => f (h * g)) k := by
  induction Xs generalizing k with
  | nil =>
    change unitsExtension f (k.val * g.val) = f (k * g)
    exact unitsExtension_val f (k * g)
  | cons X Xs ih =>
    let H := jointWord Xs (jointTranslate f)
    let V := word Xs (fun h => f (h * g))
    have hH := contDiffOn_jointWord Xs (contDiffOn_jointTranslate hf)
    have hMem : (g.val, k.val) ∈ U ×ˢ U := ⟨g.isUnit, k.isUnit⟩
    have hHdiff : DifferentiableAt ℝ H (g.val, k.val) :=
      (hH.contDiffAt ((isOpen_unitDomain.prod isOpen_unitDomain).mem_nhds
        hMem)).differentiableAt (by simp)
    have hV := RealUniformWhittaker.contMDiff_iteratedRightDerivative
      (hf.comp (contMDiff_mul_right (a := g))) Xs
    have heq : (fun z => H (g.val, z)) =ᶠ[𝓝 k.val] unitsExtension V := by
      filter_upwards [isOpen_unitDomain.mem_nhds k.isUnit] with z hz
      obtain ⟨l, rfl⟩ := hz
      rw [unitsExtension_val]
      exact ih l
    change fderiv ℝ H (g.val, k.val) (0, k.val * X) = D X V k
    rw [← Langlands.Analysis.fderiv_snd_slice_apply hHdiff, heq.fderiv_eq]
    exact (rightDerivative_eq_fderiv hV X k).symm

private theorem jointTranslate_fst_derivative {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ f) (X : Mat)
    {a b : Mat} (ha : a ∈ U) (hb : b ∈ U) :
    fderiv ℝ (fun z => jointTranslate f (z, b)) a (a * X) =
      jointTranslate (D X f) (a, b) := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hb
  have hF : DifferentiableAt ℝ (unitsExtension f) (k.val * g.val) :=
    ((contDiffOn_unitsExtension hf).contDiffAt
      (isOpen_unitDomain.mem_nhds (k.isUnit.mul g.isUnit))).differentiableAt (by simp)
  let L : Mat →L[ℝ] Mat := ContinuousLinearMap.mul ℝ Mat k.val
  have hder := hF.hasFDerivAt.comp g.val L.hasFDerivAt
  change fderiv ℝ (fun z => unitsExtension f (k.val * z)) g.val (g.val * X) =
    unitsExtension (D X f) (k.val * g.val)
  rw [show k.val * g.val = (k * g).val from rfl, unitsExtension_val,
    rightDerivative_eq_fderiv hf]
  rw [show fderiv ℝ (fun z => unitsExtension f (k.val * z)) g.val =
      (fderiv ℝ (unitsExtension f) (k.val * g.val)).comp L from hder.fderiv,
    ContinuousLinearMap.comp_apply]
  change fderiv ℝ (unitsExtension f) (k.val * g.val) (k.val * (g.val * X)) = _
  simp only [Units.val_mul, Matrix.mul_assoc]

/-- The word in the compact evaluation variable commutes with differentiation of
the translation variable, with the two directions held in their own factors. -/
private theorem jointWord_fst_derivative (Xs : List Mat) (X : Mat)
    {H F : Mat × Mat → ℂ}
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ U)) (hF : ContDiffOn ℝ ∞ F (U ×ˢ U))
    (hD : ∀ a ∈ U, ∀ b ∈ U, fderiv ℝ (fun z => H (z, b)) a (a * X) = F (a, b))
    {a b : Mat} (ha : a ∈ U) (hb : b ∈ U) :
    fderiv ℝ (fun z => jointWord Xs H (z, b)) a (a * X) = jointWord Xs F (a, b) := by
  induction Xs generalizing a b with
  | nil => exact hD a ha b hb
  | cons Y Xs ih =>
    let V := jointWord Xs H
    let W := jointWord Xs F
    have hV := contDiffOn_jointWord Xs hH
    have hW := contDiffOn_jointWord Xs hF
    have hu : IsOpen (U : Set Mat) := isOpen_unitDomain
    have hleft :
        (fun z => jointDirection Y V (z, b)) =ᶠ[𝓝 a]
          fun z => fderiv ℝ (fun q => V (z, q)) b (b * Y) := by
      filter_upwards [hu.mem_nhds ha] with z hz
      exact (Langlands.Analysis.fderiv_snd_slice_apply
        ((hV.contDiffAt ((hu.prod hu).mem_nhds ⟨hz, hb⟩)).differentiableAt (by simp))
        (b * Y)).symm
    have hright :
        (fun q => fderiv ℝ (fun z => V (z, q)) a (a * X)) =ᶠ[𝓝 b]
          fun q => W (a, q) := by
      filter_upwards [hu.mem_nhds hb] with q hq
      exact ih ha hq
    change fderiv ℝ (fun z => jointDirection Y V (z, b)) a (a * X) =
      jointDirection Y W (a, b)
    rw [hleft.fderiv_eq, Langlands.Analysis.fderiv_fst_snd_comm hu hu hV ha hb,
      hright.fderiv_eq]
    exact Langlands.Analysis.fderiv_snd_slice_apply
      ((hW.contDiffAt ((hu.prod hu).mem_nhds ⟨ha, hb⟩)).differentiableAt (by simp)) _

private theorem exists_continuous_factor {V E : Type*}
    [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ) {C : ℝ}
    (hC : ∀ v, ‖ℓ v‖ ≤ C * ‖J v‖) :
    ∃ L : E →L[ℂ] ℂ, ∀ v, L (J v) = ℓ v := by
  have hker : LinearMap.ker J ≤ LinearMap.ker ℓ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [hv, norm_zero, mul_zero] using hC v
  let F := (LinearMap.ker J).liftQ ℓ hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap
  have hFJ (v : V) : F (J.rangeRestrict v) = ℓ v := by
    change (LinearMap.ker J).liftQ ℓ hker (J.quotKerEquivRange.symm ⟨J v, ⟨v, rfl⟩⟩) = _
    rw [J.quotKerEquivRange_symm_apply_image]
    rfl
  have hF (y : LinearMap.range J) : ‖F y‖ ≤ C * ‖y‖ := by
    obtain ⟨v, hv⟩ := y.2
    have hy : J.rangeRestrict v = y := Subtype.ext hv
    rw [← hy, hFJ]
    exact hC v
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq (LinearMap.range J) (F.mkContinuous C hF)
  exact ⟨L, fun v => (hL (J.rangeRestrict v)).trans (hFJ v)⟩

variable (ds : List RealBlock)

local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter ds)
local notation "K" => unitaryCompact ℝ (r + 1)

private def compactDerivative (Xs : List Mat) : P →ₗ[ℂ] C(K, ℂ) where
  toFun f := ⟨fun k => word Xs f k,
    (RealUniformWhittaker.contMDiff_iteratedRightDerivative f.2.1 Xs).continuous.comp
      continuous_subtype_val⟩
  map_add' f f' := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_add f.2.1 f'.2.1 Xs) k.val
  map_smul' z f := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_smul f.2.1 z Xs) k.val

private def compactCoordinates {m : ℕ} (Xs : Fin m → List Mat) :
    P →ₗ[ℂ] (Fin m → C(K, ℂ)) :=
  LinearMap.pi fun i => compactDerivative ds (Xs i)

private theorem exists_compact_scalarization (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) :
    ∃ (m : ℕ) (Xs : Fin m → List Mat) (L : (Fin m → C(K, ℂ)) →L[ℂ] ℂ),
      ∀ f, L (compactCoordinates ds Xs f) = ℓ f := by
  obtain ⟨m, Xs, A, hA, hBound⟩ := hℓ
  let J := compactCoordinates ds Xs
  have hJ (f : P) : ‖ℓ f‖ ≤ (A * (m : ℝ)) * ‖J f‖ := by
    have hnorm := hBound f (fun _ => ‖J f‖) fun i k hk =>
      ((J f i).norm_coe_le_norm ⟨k, hk⟩).trans (norm_le_pi_norm (J f) i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      using hnorm
  obtain ⟨L, hL⟩ := exists_continuous_factor J ℓ hJ
  exact ⟨m, Xs, L, hL⟩

private def compactOrbit {m : ℕ} (Xs : Fin m → List Mat) (f : P) (a : Mat) :
    Fin m → C(K, ℂ) := by
  classical
  exact if ha : IsUnit a then compactCoordinates ds Xs (translate r ds ha.unit f) else 0

private theorem compactOrbit_val {m : ℕ} (Xs : Fin m → List Mat) (f : P) (g : G) :
    compactOrbit ds Xs f g.val = compactCoordinates ds Xs (translate r ds g f) := by
  simp only [compactOrbit, dite_eq_left g.isUnit]
  rw [show g.isUnit.unit = g from Units.ext g.isUnit.unit_spec]

private theorem compactOrbit_contDiffOn {m : ℕ} (Xs : Fin m → List Mat) (f : P) :
    ContDiffOn ℝ ∞ (compactOrbit ds Xs f) U := by
  apply contDiffOn_pi.2
  intro i
  let j : C(K, Mat) := ⟨fun k => k.val.val, Units.continuous_val.comp continuous_subtype_val⟩
  apply Langlands.Analysis.contDiffOn_infty_compactFamily_of_joint j isOpen_unitDomain
    isOpen_unitDomain (fun k => k.val.isUnit)
    (contDiffOn_jointWord (Xs i) (contDiffOn_jointTranslate f.2.1))
  intro a ha k
  obtain ⟨g, rfl⟩ := ha
  rw [compactOrbit_val]
  exact (jointWord_translate_value f.2.1 (Xs i) g k.val).symm

private def sourceDerivative (X : Mat) (f : P) : P :=
  ⟨D X f, rightDerivative_mem_principalSeries _ f.2 X⟩

private theorem compactOrbit_fderiv {m : ℕ} (Xs : Fin m → List Mat)
    (f : P) (g : G) (X : Mat) :
    fderiv ℝ (compactOrbit ds Xs f) g.val (g.val * X) =
      compactCoordinates ds Xs (translate r ds g (sourceDerivative ds X f)) := by
  have hg := isOpen_unitDomain.mem_nhds g.isUnit
  have hf := ((compactOrbit_contDiffOn ds Xs f).contDiffAt hg).differentiableAt (by simp)
  ext1 i
  ext1 k
  let ev : (Fin m → C(K, ℂ)) →L[ℝ] ℂ :=
    (ContinuousMap.evalCLM (R := ℝ) k).comp (ContinuousLinearMap.proj i)
  have hEval := congrArg (fun L : Mat →L[ℝ] ℂ => L (g.val * X))
    (ev.hasFDerivAt.comp g.val hf.hasFDerivAt).fderiv
  change fderiv ℝ (fun z => ev (compactOrbit ds Xs f z)) g.val (g.val * X) =
    ((fderiv ℝ (compactOrbit ds Xs f) g.val (g.val * X)) i) k at hEval
  rw [← hEval]
  have he : (fun z => ev (compactOrbit ds Xs f z)) =ᶠ[𝓝 g.val]
      fun z => jointWord (Xs i) (jointTranslate (f : G → ℂ)) (z, k.val.val) := by
    filter_upwards [hg] with z hz
    obtain ⟨q, rfl⟩ := hz
    change (compactOrbit ds Xs f q.val i) k = _
    rw [compactOrbit_val]
    exact (jointWord_translate_value f.2.1 (Xs i) q k.val).symm
  rw [he.fderiv_eq, jointWord_fst_derivative (Xs i) X (contDiffOn_jointTranslate f.2.1)
    (contDiffOn_jointTranslate (contMDiff_rightDerivative f.2.1 X))
    (fun a ha b hb => jointTranslate_fst_derivative f.2.1 X ha hb) g.isUnit k.val.isUnit]
  exact jointWord_translate_value (contMDiff_rightDerivative f.2.1 X) (Xs i) g k.val

/-- The coefficients of a compact-derivative-bounded form are smooth, and their
right derivatives are the coefficients of the derived source vectors. -/
private theorem smoothCoefficient_and_rightDerivative (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (f : P) :
    ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (fun g => ℓ (translate r ds g f)) ∧
      ∀ (X : Mat) (g : G), D X (fun q => ℓ (translate r ds q f)) g =
        ℓ (translate r ds g (sourceDerivative ds X f)) := by
  obtain ⟨m, Xs, L, hL⟩ := exists_compact_scalarization ds ℓ hℓ
  let F := compactOrbit ds Xs f
  have hF := compactOrbit_contDiffOn ds Xs f
  have hLF := (L.restrictScalars ℝ).contDiff.comp_contDiffOn hF
  have hOn : ∀ g : G, L (F g.val) = ℓ (translate r ds g f) := by
    intro g
    change L (compactOrbit ds Xs f g.val) = _
    rw [compactOrbit_val, hL]
  have hSmooth : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g => ℓ (translate r ds g f)) := by
    have hs : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (fun g : G => L (F g.val)) :=
      hLF.contMDiffOn.comp_contMDiff (Units.contMDiff_val (𝕜 := ℝ) (n := ∞))
        (fun g : G => g.isUnit)
    simpa only [hOn] using hs
  refine ⟨hSmooth, fun X g => ?_⟩
  have hg := isOpen_unitDomain.mem_nhds g.isUnit
  have hFdiff := (hF.contDiffAt hg).differentiableAt (by simp)
  have he : unitsExtension (fun q => ℓ (translate r ds q f)) =ᶠ[𝓝 g.val]
      fun a => L (F a) := by
    filter_upwards [hg] with a ha
    obtain ⟨q, rfl⟩ := ha
    rw [unitsExtension_val, hOn]
  rw [rightDerivative_eq_fderiv hSmooth, he.fderiv_eq]
  have hDer := ((L.restrictScalars ℝ).hasFDerivAt.comp g.val hFdiff.hasFDerivAt).fderiv
  rw [show fderiv ℝ (fun a => L (F a)) g.val =
      (L.restrictScalars ℝ).comp (fderiv ℝ F g.val) from hDer, ContinuousLinearMap.comp_apply]
  change L (fderiv ℝ (compactOrbit ds Xs f) g.val (g.val * X)) = _
  rw [compactOrbit_fderiv, hL]

private theorem translate_mul_apply (g h : G) (f : P) :
    translate r ds (g * h) f = translate r ds g (translate r ds h f) := by
  apply Subtype.ext
  funext k
  change (f : G → ℂ) (k * (g * h)) = (f : G → ℂ) ((k * g) * h)
  rw [mul_assoc]

private def sourceInclusion : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] P :=
  Submodule.inclusion fun _ hf => hf.1.1

/-- Coefficients of a form on the smooth position principal series, restricted
to the K-finite standard module. -/
def functionalCoefficient (ℓ : P →ₗ[ℂ] ℂ) :
    Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ) :=
  LinearMap.pi fun g => ℓ ∘ₗ translate r ds g ∘ₗ sourceInclusion ds

theorem isRealUniformWhittakerIntertwiner_functionalCoefficient (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ)
    (hψ : ∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ f : P,
      ℓ (translate r ds u f) = realWhittakerCharacter a u * ℓ f) :
    IsRealUniformWhittakerIntertwiner r ds a (functionalCoefficient ds ℓ) := by
  obtain ⟨N, hN⟩ := compactFunctionalGrowth r ds ℓ hℓ
  have hGrowth (f : Automorphic.realStandardKFinite (r + 1) ds) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ‖functionalCoefficient ds ℓ f g‖ ≤
        C * realMatrixHeight g ^ N :=
    hN (sourceInclusion ds f)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, N, hGrowth⟩
  · intro f u hu g
    change ℓ (translate r ds (u * g) (sourceInclusion ds f)) =
      realWhittakerCharacter a u * ℓ (translate r ds g (sourceInclusion ds f))
    rw [translate_mul_apply]
    exact hψ u hu _
  · intro f
    exact (smoothCoefficient_and_rightDerivative ds ℓ hℓ (sourceInclusion ds f)).1
  · intro f
    obtain ⟨C, _, hC⟩ := hGrowth f
    exact ⟨C, N, hC⟩
  · intro k f f' hk
    have hSource : sourceInclusion ds f' = translate r ds k.val (sourceInclusion ds f) :=
      Subtype.ext hk
    funext g
    change ℓ (translate r ds g (sourceInclusion ds f')) =
      ℓ (translate r ds (g * k.val) (sourceInclusion ds f))
    rw [hSource, translate_mul_apply]
  · intro X f f' hX
    have hSource : sourceInclusion ds f' = sourceDerivative ds X (sourceInclusion ds f) :=
      Subtype.ext hX
    funext g
    change ℓ (translate r ds g (sourceInclusion ds f')) =
      D X (fun q => ℓ (translate r ds q (sourceInclusion ds f))) g
    rw [hSource]
    exact ((smoothCoefficient_and_rightDerivative ds ℓ hℓ (sourceInclusion ds f)).2 X g).symm

/-- A compact-derivative-bounded Whittaker form on the smooth position principal
series gives a uniform Whittaker coefficient map of the K-finite standard module. -/
def CompactWhittakerCoefficientStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (ℓ : principalSeries ℝ (r + 1) (realPositionCharacter ds) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r ds ℓ →
    (∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ,
      ∀ f : principalSeries ℝ (r + 1) (realPositionCharacter ds),
        ℓ (translate r ds u f) = realWhittakerCharacter a u * ℓ f) →
    IsRealUniformWhittakerIntertwiner r ds a (functionalCoefficient ds ℓ)

theorem compactWhittakerCoefficient : CompactWhittakerCoefficientStatement :=
  fun _ ds => isRealUniformWhittakerIntertwiner_functionalCoefficient ds

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
