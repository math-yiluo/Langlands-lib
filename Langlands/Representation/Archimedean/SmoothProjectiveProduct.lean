import Langlands.Representation.Archimedean.CompletedProjectiveRepresentation
import Langlands.Representation.Archimedean.SmoothDerivativeFunctional
import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Langlands.Geometry.Manifold.LinearLieGroup.Exponential
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Separate differentiation on the smooth part of a projective tensor product -/

noncomputable section

open scoped ContDiff Manifold TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Archimedean.CompletedProjectiveRepresentation

open DerivativeSmoothVectors
open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)
open Langlands.LinearLieGroup (expUnit coe_expUnit)
open NormedSpace (exp)

private theorem hasDerivAt_exponentialOrbit {A E : Type*}
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [FiniteDimensional ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : Aˣ →* (E →L[ℂ] E)) (hR : IsContinuousRepresentation R)
    (X : A) (v : DerivativeSmoothVectors 𝓘(ℝ, A) R) :
    HasDerivAt (fun t : ℝ => R (expUnit A (t • X)) (toSmooth 𝓘(ℝ, A) R v))
      ((toSmooth 𝓘(ℝ, A) R (operator 𝓘(ℝ, A) R X v)) : E) 0 := by
  have hc : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h := hasDerivAt_unitsChartOrbit R hR 1 v hc (by simp)
  let P := (derivativeCLM 𝓘(ℝ, A) R []).restrictScalars ℝ
  have hp : HasDerivAt (fun t : ℝ => P (unitsChartAction R (exp (t • X), v)))
      (P (representation 𝓘(ℝ, A) R 1 (operator 𝓘(ℝ, A) R ((1 : Aˣ)⁻¹.val * X) v))) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_tvs] at h ⊢
    refine (P.continuous.tendsto _ |>.comp h).congr ?_
    intro t
    simp [slope_def_module, map_sub]
  simpa only [P, ContinuousLinearMap.coe_restrictScalars', derivativeCLM_apply,
    iteratedLieDerivative_nil, inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply,
    ← coe_expUnit, unitsChartAction_val, toSmooth_representation, smoothRepresentation_apply] using hp

universe uι uA uE

variable {ι : Type uι} [Fintype ι]
  (A : ι → Type uA) [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℝ (A i)]
  [∀ i, CompleteSpace (A i)]
  {E : ι → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, (A i)ˣ →* (E i →L[ℂ] E i))

local notation "U" => (∀ i, A i)ˣ
local notation "I" => 𝓘(ℝ, (∀ i, A i))
local notation "I₀" => fun i => 𝓘(ℝ, A i)

/-- The unit-group homomorphism induced by evaluating one coordinate of the algebra. -/
def unitProjection (i : ι) : U →* (A i)ˣ :=
  Units.map (Pi.evalRingHom A i).toMonoidHom

omit [Fintype ι] [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] in
@[simp] theorem unitProjection_val (i : ι) (g : U) : (unitProjection A i g).val = g.val i := rfl

private theorem contMDiff_unitProjection (i : ι) :
    ContMDiff I (I₀ i) ∞ (unitProjection A i) := by
  let P : (∀ j, A j) →L[ℝ] A i := ContinuousLinearMap.proj i
  have h := P.contDiff.contMDiff.comp (Units.contMDiff_val (n := ∞) (𝕜 := ℝ))
  rw [contMDiff_iff_target]
  refine ⟨?_, fun y => ?_⟩
  · rw [Units.isOpenEmbedding_val.isEmbedding.continuous_iff]
    exact h.continuous
  · have he : extChartAt (I₀ i) y ∘ unitProjection A i = fun g : U => P (g.val) := by
      funext g
      simp [extChartAt, P]
    rw [he]
    exact h.contMDiffOn

/-- The action of the units of the product algebra on the completed product. -/
def productAction : U →* (Carrier E →L[ℂ] Carrier E) :=
  action (fun i => (R i).comp (unitProjection A i))

omit [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] in
@[simp] theorem productAction_pure (g : U) (v : ∀ i, E i) :
    productAction A R g (pure E v) = pure E (fun i => R i (unitProjection A i g) (v i)) :=
  action_pure _ g v

/-- The product action is jointly continuous for a finite family of continuous Banach actions. -/
theorem isContinuous_productAction [∀ i, FiniteDimensional ℝ (A i)] [∀ i, CompleteSpace (E i)]
    (hR : ∀ i, IsContinuousRepresentation (R i)) : IsContinuousRepresentation (productAction A R) := by
  let : LocallyCompactSpace U := Units.isOpenEmbedding_val.locallyCompactSpace
  exact isContinuous_action _ fun i =>
    (hR i).comp (((contMDiff_unitProjection A i).continuous.comp continuous_fst).prodMk continuous_snd)

local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "D₀" => fun i => DerivativeSmoothVectors (I₀ i) (R i)

/-- A pure product of genuine smooth vectors in the smooth carrier for the product group. -/
def pureSmooth (v : ∀ i, D₀ i) : D :=
  (toSmooth I (productAction A R)).symm
    ⟨pure E (fun i => toSmooth (I₀ i) (R i) (v i)),
      isSmoothVector_pure _ I _ fun i => ((toSmooth (I₀ i) (R i) (v i)).property).comp
        (contMDiff_unitProjection A i)⟩

@[simp] theorem toSmooth_pureSmooth (v : ∀ i, D₀ i) :
    ((toSmooth I (productAction A R) (pureSmooth A R v)) : Carrier E) =
      pure E (fun i => toSmooth (I₀ i) (R i) (v i)) := rfl

variable [DecidableEq ι]

private theorem unitProjection_exp_single (i j : ι) (X : A i) (t : ℝ) :
    unitProjection A j (expUnit (∀ k, A k) (t • Pi.single i X)) =
      Function.update (fun k => (1 : (A k)ˣ)) i (expUnit (A i) (t • X)) j := by
  apply Units.ext
  have he := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (Pi.evalRingHom A j) (continuous_apply j)
    (x := t • Pi.single i X) (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  change exp (t • Pi.single i X) j = exp (t • Pi.single i X j) at he
  rw [unitProjection_val, coe_expUnit, he]
  by_cases h : j = i
  · subst j
    simp
  · rw [Pi.single_eq_of_ne h, smul_zero, NormedSpace.exp_zero, Function.update_of_ne h]
    rfl

/-- A Lie derivative in one factor differentiates that factor of a pure smooth tensor. -/
theorem operator_axial_pureSmooth
    [∀ i, FiniteDimensional ℝ (A i)]
    (hP : IsContinuousRepresentation (productAction A R))
    (hR : ∀ i, IsContinuousRepresentation (R i)) (v : ∀ i, D₀ i) (i : ι) (X : A i) :
    operator I (productAction A R) (Pi.single i X) (pureSmooth A R v) =
      pureSmooth A R (Function.update v i (operator (I₀ i) (R i) X (v i))) := by
  let w : ∀ i, E i := fun j => toSmooth (I₀ j) (R j) (v j)
  let P := ((pure E).toContinuousLinearMap w i).restrictScalars ℝ
  have h₁ := hasDerivAt_exponentialOrbit (productAction A R) hP (Pi.single i X) (pureSmooth A R v)
  have h₂ := P.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exponentialOrbit (R i) (hR i) X (v i))
  have he : (fun t : ℝ => productAction A R (expUnit (∀ j, A j) (t • Pi.single i X))
      (toSmooth I (productAction A R) (pureSmooth A R v))) =
      fun t : ℝ => P (R i (expUnit (A i) (t • X)) (w i)) := by
    funext t
    rw [toSmooth_pureSmooth, productAction_pure]
    simp only [P, ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.toContinuousLinearMap_apply]
    congr 1
    funext j
    rw [unitProjection_exp_single]
    by_cases h : j = i
    · subst j
      simp [w]
    · simp [h, w]
  rw [he] at h₁
  apply (toSmooth I (productAction A R)).injective
  apply Subtype.ext
  rw [toSmooth_pureSmooth, h₁.unique h₂]
  simp only [P, ContinuousLinearMap.coe_restrictScalars', ContinuousMultilinearMap.toContinuousLinearMap_apply]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h, w]

private def axisComponent (j : ι) (p : Σ i, A i) : Option (A j) :=
  if h : p.1 = j then some (h ▸ p.2) else none

private theorem derivativeCoordinates_pureSmooth_tagged
    [∀ i, FiniteDimensional ℝ (A i)]
    (hP : IsContinuousRepresentation (productAction A R))
    (hR : ∀ i, IsContinuousRepresentation (R i)) (v : ∀ i, D₀ i) (w : List (Σ i, A i)) :
    derivativeCoordinates I (productAction A R) (pureSmooth A R v)
        (w.map fun p => Pi.single p.1 p.2) =
      pure E (fun i => derivativeCoordinates (I₀ i) (R i) (v i) (w.filterMap (axisComponent A i))) := by
  induction w using List.reverseRecOn generalizing v with
  | nil => rfl
  | append_singleton w p ih =>
    obtain ⟨i, X⟩ := p
    simp only [List.map_append, List.map_singleton]
    rw [← derivativeCoordinates_operator, operator_axial_pureSmooth A R hP hR, ih]
    apply congrArg (pure E)
    funext j
    by_cases h : i = j
    · subst j
      rw [Function.update_self, derivativeCoordinates_operator]
      simp [axisComponent]
    · simp [axisComponent, h, Ne.symm h]

/-- Concatenate a tuple of words using the Lie algebra inclusions of the individual factors. -/
def embeddedWords (w : ∀ i, List (A i)) : List (∀ i, A i) :=
  ((Finset.univ.toList : List ι).flatMap fun i => (w i).map (Sigma.mk i)).map
    fun p => Pi.single p.1 p.2

omit [Fintype ι] [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] in
private theorem filterMap_axisComponent (w : ∀ i, List (A i)) (j : ι) (l : List ι) (hn : l.Nodup) :
    (l.flatMap fun i => (w i).map (Sigma.mk i)).filterMap (axisComponent A j) =
      if j ∈ l then w j else [] := by
  induction l with
  | nil => simp
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hn
    rw [List.flatMap_cons, List.filterMap_append, ih hl, List.filterMap_map]
    by_cases h : i = j
    · subst i
      simp [axisComponent, hi]
    · have hNone : axisComponent A j ∘ Sigma.mk i = fun _ => none := by
        funext x
        simp [axisComponent, h]
      rw [hNone]
      simp [Ne.symm h]

/-- Applying the mixed word in the completed product applies the prescribed word in each factor. -/
theorem derivativeCoordinates_pureSmooth
    [∀ i, FiniteDimensional ℝ (A i)]
    (hP : IsContinuousRepresentation (productAction A R))
    (hR : ∀ i, IsContinuousRepresentation (R i)) (v : ∀ i, D₀ i)
    (w : ∀ i, List (A i)) :
    derivativeCoordinates I (productAction A R) (pureSmooth A R v) (embeddedWords A w) =
      pure E (fun i => derivativeCoordinates (I₀ i) (R i) (v i) (w i)) := by
  rw [embeddedWords, derivativeCoordinates_pureSmooth_tagged A R hP hR]
  apply congrArg (pure E)
  funext i
  rw [filterMap_axisComponent A w i _ (Finset.nodup_toList _)]
  simp

/-- Products of continuous smooth scalar forms extend to the genuine smooth part of the completed
projective tensor product, using the product group action. -/
def SmoothProjectiveProductFunctionalStatement : Prop :=
  ∀ {ι : Type uι} [Fintype ι] (A : ι → Type uA) [∀ i, NormedRing (A i)]
    [∀ i, NormedAlgebra ℝ (A i)] [∀ i, CompleteSpace (A i)] [∀ i, FiniteDimensional ℝ (A i)]
    (E : ι → Type uE) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (R : ∀ i, (A i)ˣ →* (E i →L[ℂ] E i)),
    (∀ i, IsContinuousRepresentation (R i)) →
    ∀ L : ∀ i, DerivativeSmoothVectors 𝓘(ℝ, A i) (R i) →L[ℂ] ℂ,
      ∃ T : DerivativeSmoothVectors 𝓘(ℝ, (∀ i, A i)) (productAction A R) →L[ℂ] ℂ,
        ∀ v : ∀ i, DerivativeSmoothVectors 𝓘(ℝ, A i) (R i),
          T (pureSmooth A R v) = ∏ i, L i (v i)

set_option maxHeartbeats 450000 in
theorem smoothProjectiveProductFunctional : SmoothProjectiveProductFunctionalStatement := by
  intro ι _ A _ _ _ _ E _ _ _ R hR L
  classical
  have hP := isContinuous_productAction A R hR
  choose J T hT using fun i : ι => smoothDerivativeFunctional 𝓘(ℝ, A i) (R i) (L i)
  let F (i : ι) (p : J i) : E i →L[ℂ] ℂ :=
    (T i).comp (ContinuousLinearMap.single ℂ (fun _ : J i => E i) p)
  let B (p : ∀ i, J i) : ContinuousMultilinearMap ℂ E ℂ :=
    (ContinuousMultilinearMap.mkPiAlgebra ℂ ι ℂ).compContinuousLinearMap (fun i => F i (p i))
  let S (p : ∀ i, J i) : DerivativeSmoothVectors 𝓘(ℝ, (∀ i, A i)) (productAction A R) →L[ℂ] ℂ :=
    (lift (B p)).comp (derivativeCLM 𝓘(ℝ, (∀ i, A i)) (productAction A R)
      (embeddedWords A (fun i => (p i).val)))
  refine ⟨∑ p, S p, fun v => ?_⟩
  have hF (i : ι) : L i (v i) =
      ∑ p : J i, F i p (derivativeCoordinates 𝓘(ℝ, A i) (R i) (v i) p.val) := by
    rw [hT i (v i)]
    exact (ContinuousLinearMap.sum_comp_single ℂ (fun _ : J i => E i) (T i) _).symm
  simp_rw [hF, Fintype.prod_sum]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  change lift (B p) (derivativeCoordinates 𝓘(ℝ, (∀ i, A i)) (productAction A R) (pureSmooth A R v)
    (embeddedWords A (fun i => (p i).val))) = _
  rw [derivativeCoordinates_pureSmooth A R hP hR, lift_pure]
  rfl

end Langlands.Archimedean.CompletedProjectiveRepresentation
