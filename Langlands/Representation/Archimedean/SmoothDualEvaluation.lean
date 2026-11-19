import Langlands.Representation.Archimedean.HilbertContragredientContinuity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Evaluation between the smooth original and continuous-dual representations -/

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff InnerProduct ComplexConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

section DualAction

variable {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (R : G →* (E →L[ℂ] E))

/-- The action on continuous complex linear functionals by inverse precomposition. -/
def continuousDualRepresentation : G →* (StrongDual ℂ E →L[ℂ] StrongDual ℂ E) where
  toFun g := (ContinuousLinearMap.compSL E E ℂ (RingHom.id ℂ) (RingHom.id ℂ)).flip (R g⁻¹)
  map_one' := by
    ext L v
    change L (R (1 : G)⁻¹ v) = L v
    simp
  map_mul' g h := by
    ext L v
    change L (R (g * h)⁻¹ v) = L (R h⁻¹ (R g⁻¹ v))
    rw [mul_inv_rev, map_mul, mul_apply_eq_comp]

@[simp]
theorem continuousDualRepresentation_apply (g : G) (L : StrongDual ℂ E) (v : E) :
    continuousDualRepresentation R g L v = L (R g⁻¹ v) :=
  rfl

end DualAction

section Riesz

variable {G : Type*} [Group G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : G →* (H →L[ℂ] H))

/-- Riesz identification intertwines the inverse-adjoint model and inverse precomposition. -/
theorem toDual_hilbertContragredient (g : G) (v : H) :
    InnerProductSpace.toDual ℂ H (hilbertContragredient R g v) =
      continuousDualRepresentation R g (InnerProductSpace.toDual ℂ H v) := by
  ext w
  exact inner_hilbertContragredient R g v w

private def realLinearOfConjugateLinear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L⋆[ℂ] F) : E →L[ℝ] F where
  toFun := L
  map_add' := L.map_add
  map_smul' c x := by
    change L ((c : ℂ) • x) = (c : ℂ) • L x
    rw [map_smulₛₗ]
    congr 1
    exact Complex.conj_ofReal c
  cont := L.continuous

variable [TopologicalSpace G]

/-- Joint continuity passes from the inverse-adjoint Hilbert model to the continuous dual. -/
theorem isContinuousRepresentation_continuousDual_of_adjoint
    (h : IsContinuousRepresentation (hilbertContragredient R)) :
    IsContinuousRepresentation (continuousDualRepresentation R) := by
  let e := InnerProductSpace.toDual ℂ H
  have hh : Continuous fun p : G × H => hilbertContragredient R p.1 p.2 := h
  have hp : Continuous fun p : G × StrongDual ℂ H => (p.1, e.symm p.2) :=
    continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)
  have hi := hh.comp hp
  have hc := e.continuous.comp hi
  change Continuous fun p : G × StrongDual ℂ H => continuousDualRepresentation R p.1 p.2
  refine hc.congr fun p => ?_
  change e (hilbertContragredient R p.1 (e.symm p.2)) = _
  rw [toDual_hilbertContragredient, LinearIsometryEquiv.apply_symm_apply]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- Smoothness of a Riesz functional for inverse precomposition is exactly smoothness of
its representing vector for the inverse-adjoint action. -/
theorem isSmoothVector_toDual_iff (R' : Aˣ →* (H →L[ℂ] H)) (v : H) :
    IsSmoothVector 𝓘(ℝ, A) (continuousDualRepresentation R') (InnerProductSpace.toDual ℂ H v) ↔
      IsSmoothVector 𝓘(ℝ, A) (hilbertContragredient R') v := by
  let e := InnerProductSpace.toDual ℂ H
  let E := realLinearOfConjugateLinear e.toContinuousLinearEquiv.toContinuousLinearMap
  let F := realLinearOfConjugateLinear e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have he (g : Aˣ) : E (hilbertContragredient R' g v) =
      continuousDualRepresentation R' g (e v) := toDual_hilbertContragredient R' g v
  have hf (g : Aˣ) : F (continuousDualRepresentation R' g (e v)) =
      hilbertContragredient R' g v := by
    rw [← he]
    exact e.symm_apply_apply _
  constructor
  · intro h
    have h' := F.contDiff.contMDiff.comp h
    change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, H) ∞
      (fun g => F (continuousDualRepresentation R' g (e v))) at h'
    change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, H) ∞ (fun g => hilbertContragredient R' g v)
    simpa only [hf] using h'
  · intro h
    have h' := E.contDiff.contMDiff.comp h
    change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, StrongDual ℂ H) ∞
      (fun g => E (hilbertContragredient R' g v)) at h'
    change ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, StrongDual ℂ H) ∞
      (fun g => continuousDualRepresentation R' g (e v))
    simpa only [he] using h'

/-- The action on the continuous complex dual of an actual continuous Hilbert
representation of units of a finite-dimensional real Banach algebra is jointly continuous. -/
theorem isContinuousRepresentation_continuousDual [FiniteDimensional ℝ A]
    (R' : Aˣ →* (H →L[ℂ] H)) (hR : IsContinuousRepresentation R') :
    IsContinuousRepresentation (continuousDualRepresentation R') :=
  isContinuousRepresentation_continuousDual_of_adjoint R'
    (isContinuousRepresentation_hilbertContragredient R' hR)

end Riesz

section SmoothEvaluation

open DerivativeSmoothVectors

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "Ddual" => DerivativeSmoothVectors 𝓜 (continuousDualRepresentation R)
local notation "ε" => derivativeCLM 𝓜 R []
local notation "εdual" => derivativeCLM 𝓜 (continuousDualRepresentation R) []

/-- Bilinear evaluation of genuine smooth original vectors by genuine smooth continuous
functionals. Each input is given its original normed value by the empty word. -/
def smoothDualEvaluation : D →ₗ[ℂ] Ddual →ₗ[ℂ] ℂ where
  toFun v :=
    { toFun := fun L => εdual L (ε v)
      map_add' := fun L M => by rw [map_add, add_apply]
      map_smul' := fun c L => by rw [map_smul, smul_apply, RingHom.id_apply] }
  map_add' v w := by
    ext L
    change εdual L (ε (v + w)) = εdual L (ε v) + εdual L (ε w)
    rw [map_add, map_add]
  map_smul' c v := by
    ext L
    change εdual L (ε (c • v)) = c • εdual L (ε v)
    rw [map_smul, map_smul]

@[simp]
theorem smoothDualEvaluation_apply (v : D) (L : Ddual) :
    smoothDualEvaluation R v L = εdual L (ε v) :=
  rfl

/-- Evaluation is jointly continuous in the two genuine word-derivative topologies. -/
theorem continuous_smoothDualEvaluation :
    Continuous (fun p : D × Ddual => smoothDualEvaluation R p.1 p.2) :=
  ((εdual).continuous.comp continuous_snd).clm_apply ((ε).continuous.comp continuous_fst)

/-- Evaluation is invariant under the original action and the continuous dual action. -/
theorem smoothDualEvaluation_representation (g : Aˣ) (v : D) (L : Ddual) :
    smoothDualEvaluation R (representation 𝓜 R g v)
      (representation 𝓜 (continuousDualRepresentation R) g L) = smoothDualEvaluation R v L := by
  change continuousDualRepresentation R g (εdual L) (R g (ε v)) = εdual L (ε v)
  rw [continuousDualRepresentation_apply, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

variable [FiniteDimensional ℝ A]

private theorem hasDerivAt_emptyWord_line (hR : IsContinuousRepresentation R) (X : A) (v : D) :
    HasDerivAt (fun t : ℝ => ε (unitsChartAction R (1 + t • X, v)))
      (ε (operator 𝓜 R X v)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
    simpa only [id, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : A)
  have h := hasDerivAt_unitsChartOrbit R hR 1 v hc (by simp)
  rw [Langlands.Analysis.hasDerivAt_iff_tendsto_slope_tvs] at h ⊢
  let p := fun t : ℝ => unitsChartAction R (1 + t • X, v)
  let E₀ := (ε).restrictScalars ℝ
  have h' := (E₀.continuous.tendsto _).comp h
  change Filter.Tendsto (slope ((E₀ : D →ₗ[ℝ] E) ∘ p) 0) _
    (𝓝 (E₀ (operator 𝓜 R X v)))
  simpa only [inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply]
    using h'.congr (fun t =>
      ((E₀ : D →ₗ[ℝ] E).slope_comp p 0 t).symm)

/-- Genuine derivatives of the two actions are negatives across the smooth evaluation. -/
theorem smoothDualEvaluation_operator (hR : IsContinuousRepresentation R)
    (hD : IsContinuousRepresentation (continuousDualRepresentation R)) (X : A)
    (v : D) (L : Ddual) :
    smoothDualEvaluation R (operator 𝓜 R X v) L +
      smoothDualEvaluation R v (operator 𝓜 (continuousDualRepresentation R) X L) = 0 := by
  let c := fun t : ℝ => (unitsValueChart A).symm (1 + t • X)
  let res : StrongDual ℂ E →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E ℂ ℝ ℝ).toContinuousLinearMap
  have hL := res.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_emptyWord_line (continuousDualRepresentation R) hD X L)
  have h := hL.clm_apply (hasDerivAt_emptyWord_line R hR X v)
  have hc : c 0 = 1 := by
    simpa only [c, zero_smul, add_zero, Units.val_one] using unitsValueChart_symm_val (1 : Aˣ)
  have hev :
      (fun t : ℝ => res (εdual (unitsChartAction (continuousDualRepresentation R) (1 + t • X, L)))
          (ε (unitsChartAction R (1 + t • X, v)))) = fun _ => smoothDualEvaluation R v L :=
    funext fun t => smoothDualEvaluation_representation R (c t) v L
  have hconst := (hasDerivAt_const (0 : ℝ) (smoothDualEvaluation R v L)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (congrFun hev))
  have hz := h.unique hconst
  change εdual (operator 𝓜 (continuousDualRepresentation R) X L) (R (c 0) (ε v)) +
    continuousDualRepresentation R (c 0) (εdual L) (ε (operator 𝓜 R X v)) = 0 at hz
  simpa only [hc, map_one, one_apply_eq_self, smoothDualEvaluation_apply, add_comm] using hz

variable [CompleteSpace E]

private theorem denseRange_emptyWord (hR : IsContinuousRepresentation R) : DenseRange ε := by
  let : MeasurableSpace Aˣ := borel Aˣ
  let : BorelSpace Aˣ := ⟨rfl⟩
  let : LocallyCompactSpace Aˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  have h := dense_smoothVectors_units R (Measure.haar : Measure Aˣ) hR
  exact h.denseRange_val.comp (toSmooth 𝓜 R).surjective.denseRange continuous_subtype_val

/-- Norm density of both genuine smooth carriers makes the evaluation nondegenerate. -/
theorem nondegenerate_smoothDualEvaluation (hR : IsContinuousRepresentation R)
    (hD : IsContinuousRepresentation (continuousDualRepresentation R)) :
    (smoothDualEvaluation R).Nondegenerate := by
  constructor
  · intro v h
    have hz : ∀ L : StrongDual ℂ E, L (ε v) = 0 := by
      have he : (fun L : StrongDual ℂ E => L (ε v)) = fun _ => (0 : ℂ) := by
        apply (denseRange_emptyWord (continuousDualRepresentation R) hD).equalizer
          (ContinuousLinearMap.apply ℂ ℂ (ε v)).continuous continuous_const
        exact funext h
      exact congrFun he
    have hv : ε v = 0 := by
      by_contra hn
      obtain ⟨L, -, hL⟩ := exists_dual_vector ℂ (ε v) (norm_ne_zero_iff.mpr hn)
      rw [hz L] at hL
      have hnorm : ‖ε v‖ = 0 := by
        simpa only [norm_algebraMap', norm_norm, norm_zero] using
          (congrArg (fun z : ℂ => ‖z‖) hL).symm
      exact hn (norm_eq_zero.mp hnorm)
    apply (toSmooth 𝓜 R).injective
    apply Subtype.ext
    exact hv
  · intro L h
    have hz : εdual L = 0 := by
      ext v
      have he : (fun v : E => εdual L v) = fun _ => (0 : ℂ) := by
        apply (denseRange_emptyWord R hR).equalizer (εdual L).continuous continuous_const
        exact funext h
      exact congrFun he v
    apply (toSmooth 𝓜 (continuousDualRepresentation R)).injective
    apply Subtype.ext
    exact hz

end SmoothEvaluation

end Langlands.Archimedean
