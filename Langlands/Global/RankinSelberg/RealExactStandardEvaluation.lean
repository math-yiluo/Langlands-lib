import Langlands.Global.RankinSelberg.RealWhittakerFiniteOrder
import Langlands.Global.RankinSelberg.RealCompactDerivativeDifferences
import Langlands.Global.RankinSelberg.RealExactCompactProjection
import Langlands.Global.RankinSelberg.RealSmoothWhittakerEvaluation
import Langlands.Representation.Archimedean.SmoothCompactOrbitIntegral
import Langlands.Representation.Archimedean.SmoothKFiniteAdmissibility
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial

/-!
# Continuous Whittaker evaluation of real character principal series

For a real character list, every specified real Whittaker intertwiner of the compact-finite
standard module is evaluated by a continuous functional on the genuine smooth vectors of the
compact Banach completion. The finite-order bound of the identity evaluation, converted into
finitely many derivative suprema on the compact group, extends by Hahn--Banach. Compact
polynomial averages and the exact compact projection identify the translated evaluations, and
density of compact-finite vectors gives the Whittaker covariance.
-/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealExactStandardEvaluation

open DerivativeSmoothVectors RealStandardCompactBanach
open OrthogonalFinitePolynomial (polynomialStar polynomialStar_toSubalgebra separated
  inv_mul_mem_separated eq_zero_of_integral_polynomial_mul_eq_zero)
open RealPrincipalSeriesDuality (haarK)
open RealLocalWhittaker (iteratedRightDerivative)
open RealCompactDerivativeDifferences (word WordBound realCompactDerivativeDifferences)
open RealWhittakerFiniteOrder (realWhittakerFiniteOrder)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local instance realExactStandardMeasurable (j : ℕ) : MeasurableSpace (unitaryCompact ℝ j) :=
  borel _
local instance realExactStandardBorel (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "Kc" => unitaryCompact ℝ (r + 1)
local notation "I" => matrixModel ℝ (r + 1)
local notation "Idx" => Fin (r + 1) × Fin (r + 1)
local notation:max "S" ds:max => realStandardModule (r + 1) ds
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "act" ds:max => DerivativeSmoothVectors.representation I (R ds)

/-! ## Compact values of the derivative coordinates -/

/-- The compact values of a genuine word coordinate of a smooth standard vector are the
iterated right derivatives of the standard function. -/
theorem derivativeCLM_compactEval (ds : List RealBlock) (Xs : List M) (f : S ds) (k : U) :
    (derivativeCLM I (R ds) Xs (derivativeEquiv ds f)).val k =
      iteratedRightDerivative r Xs f.val (Unitary.toUnits k) :=
  RealStandardCompactBanach.derivativeCLM_compactEval ds Xs f k

theorem injective_derivativeCLM_nil (ds : List RealBlock) :
    Function.Injective (derivativeCLM I (R ds) []) := by
  intro x y h
  apply (toSmooth I (R ds)).injective
  apply Subtype.ext
  simpa only [derivativeCLM_apply, iteratedLieDerivative_nil] using h

/-! ## Compact averages of a translated compact-finite vector -/

/-- Right multiplication of the compact group by a fixed group element. -/
def compactTranslate (g : G) : C(Kc, G) :=
  ⟨fun k => k.val * g, continuous_subtype_val.mul continuous_const⟩

/-- A compact average of a translated compact-finite vector is the compact-finite vector with
the same values. -/
theorem compactSmoothAverage_eq (ds : List RealBlock) (κ : C(Kc, ℂ)) (f p : V ds) (g : G)
    (hp : ∀ x, p.val x = ∫ k, κ k * f.val (x * k.val * g) ∂haarK (r + 1)) :
    compactSmoothAverage (R ds) (isContinuousRepresentation ds) (haarK (r + 1))
        (compactTranslate g) κ (compactFiniteEquiv ds f).val =
      (compactFiniteEquiv ds p).val := by
  apply injective_derivativeCLM_nil ds
  rw [derivativeCLM_nil_compactSmoothAverage, compactWeightedOrbit_apply, compactFiniteEquiv_val,
    compactFiniteEquiv_val, derivativeCLM_apply, derivativeCLM_apply, iteratedLieDerivative_nil,
    iteratedLieDerivative_nil, toSmooth_derivativeEquiv, toSmooth_derivativeEquiv]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  have hi := integrable_compactWeightedOrbit (haarK (r + 1)) (R ds) (isContinuousRepresentation ds)
    (compactTranslate g) κ (embed ds ⟨f.val, f.property.1⟩)
  change profileEval ds x (∫ k, κ k • (R ds) (compactTranslate g k)
      (embed ds ⟨f.val, f.property.1⟩) ∂haarK (r + 1)) = (embed ds ⟨p.val, p.property.1⟩).val x
  rw [← (profileEval ds x).integral_comp_comm hi, embed_val, compactRestriction_apply, hp]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  simp only [map_smul, profileEval_apply, representation_embed, embed_val,
    compactRestriction_apply, translate_apply, smul_eq_mul, compactTranslate,
    ContinuousMap.coe_mk, mul_assoc]

/-! ## Polynomial compact weights -/

private theorem exists_separated_row_span {f : U → U → ℂ} (hf : f ∈ separated (r + 1)) :
    ∃ W : Submodule ℂ C(U, ℂ), FiniteDimensional ℂ W ∧ ∀ k, ∃ w ∈ W, ∀ x, w x = f k x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, _, β, rfl⟩ := hf
    refine ⟨ℂ ∙ β, inferInstance, fun k => ?_⟩
    exact ⟨α k • β, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self β), fun _ => rfl⟩
  | zero => exact ⟨⊥, inferInstance, fun _ => ⟨0, zero_mem _, fun _ => rfl⟩⟩
  | add f g _ _ hf hg =>
    obtain ⟨W, hW, h⟩ := hf
    obtain ⟨W', hW', h'⟩ := hg
    let := hW
    let := hW'
    refine ⟨W ⊔ W', inferInstance, fun k => ?_⟩
    obtain ⟨v, hv, he⟩ := h k
    obtain ⟨w, hw, he'⟩ := h' k
    refine ⟨v + w, Submodule.add_mem_sup hv hw, fun x => ?_⟩
    simp only [ContinuousMap.add_apply, Pi.add_apply, he, he']
  | smul c f _ hf =>
    obtain ⟨W, hW, h⟩ := hf
    refine ⟨W, hW, fun k => ?_⟩
    obtain ⟨v, hv, he⟩ := h k
    refine ⟨c • v, W.smul_mem c hv, fun x => ?_⟩
    simp only [ContinuousMap.smul_apply, Pi.smul_apply, he]

/-- A continuous function of orthogonal matrices, read on the compact subgroup. -/
def compactWeight (φ : C(U, ℂ)) : C(Kc, ℂ) :=
  φ.comp ⟨unitaryCompactMatrix ℝ (r + 1), continuous_unitaryCompactMatrix ℝ (r + 1)⟩

/-- A polynomial weight has finite-dimensional span of left translates. -/
theorem finiteDimensional_compactWeight {φ : C(U, ℂ)} (hφ : φ ∈ polynomialStar (r + 1)) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun h : Kc => fun k => compactWeight φ (h⁻¹ * k))) := by
  have hφ' : φ ∈ (polynomialStar (r + 1)).toSubalgebra := hφ
  rw [polynomialStar_toSubalgebra] at hφ'
  obtain ⟨W, hW, hRows⟩ := exists_separated_row_span (inv_mul_mem_separated hφ')
  let P : C(U, ℂ) →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun w k => w (unitaryCompactMatrix ℝ (r + 1) k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let := hW
  apply Submodule.finiteDimensional_of_le (S₂ := W.map P)
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  obtain ⟨w, hw, hEq⟩ := hRows (unitaryCompactMatrix ℝ (r + 1) h)
  refine ⟨w, hw, ?_⟩
  funext k
  change w (unitaryCompactMatrix ℝ (r + 1) k) =
    φ (unitaryCompactMatrix ℝ (r + 1) (h⁻¹ * k))
  rw [hEq, map_mul (unitaryCompactMatrix ℝ (r + 1)) h⁻¹ k,
    map_inv (unitaryCompactMatrix ℝ (r + 1)) h]

variable (r) in
/-- The normalized Haar measure of the compact subgroup, transported to orthogonal matrices. -/
def orthogonalHaar : Measure (Matrix.unitaryGroup (Fin (r + 1)) ℝ) :=
  (haarK (r + 1)).map (unitaryCompactMatrix ℝ (r + 1))

instance isHaarMeasure_orthogonalHaar : (orthogonalHaar r).IsHaarMeasure :=
  Measure.isHaarMeasure_map (haarK (r + 1)) (unitaryCompactMatrix ℝ (r + 1))
    (continuous_unitaryCompactMatrix ℝ (r + 1)) (unitaryCompactMatrix_surjective ℝ (r + 1))
    (by rw [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)

/-! ## Continuity of translated evaluations -/

/-- A continuous functional of genuine smooth vectors is continuous along every orbit. -/
theorem continuous_apply_representation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (P : Langlands.GeneralLinear (r + 1) ℝ →* (E →L[ℂ] E))
    (hP : IsContinuousRepresentation P) (L : DerivativeSmoothVectors I P →L[ℂ] ℂ)
    (v : DerivativeSmoothVectors I P) :
    Continuous fun h : G => L (DerivativeSmoothVectors.representation I P h v) := by
  have hA : Continuous (fun p : G × DerivativeSmoothVectors I P =>
      DerivativeSmoothVectors.representation I P p.1 p.2) :=
    continuous_representation_units P hP
  exact L.continuous.comp (hA.comp (continuous_id.prodMk continuous_const))

/-! ## The continuous evaluation -/

set_option maxHeartbeats 1000000 in
/-- A finite compact difference order of the identity evaluation gives a continuous functional
of genuine smooth vectors restricting to the identity evaluation on compact-finite vectors. -/
theorem exists_continuous_identityEvaluation (ds : List RealBlock)
    (B : (V ds) →ₗ[ℂ] (G → ℂ)) (J : ℕ) (Df : ℝ) (hDf : 0 ≤ Df)
    (hOrder : ∀ (f : V ds) (c : ℝ), RealCompactDifferences.CompactDifferenceBound J f c →
      ‖B f 1‖ ≤ Df * c) :
    ∃ L : (D ds) →L[ℂ] ℂ, ∀ f : V ds, L (compactFiniteEquiv ds f).val = B f 1 := by
  classical
  obtain ⟨Cd, hCd, hDiff⟩ := realCompactDerivativeDifferences r ds J
  let T : Finset (List Idx) := (List.finite_length_le Idx J).toFinset
  let Ws : Finset (List M) := T.image word
  let Φ : (V ds) →ₗ[ℂ] Langlands.Archimedean.smoothVectors I (R ds) :=
    (toSmooth I (R ds)).toLinearMap.comp ((smoothKFinite ℝ (r + 1) (R ds)).subtype.comp
      (compactFiniteEquiv ds).toLinearMap)
  have hΦ : Function.Injective Φ :=
    (toSmooth I (R ds)).injective.comp
      (Subtype.val_injective.comp (compactFiniteEquiv ds).injective)
  let ι := LinearEquiv.ofInjective Φ hΦ
  let ℓ₀ : LinearMap.range Φ →ₗ[ℂ] ℂ := ((LinearMap.proj 1).comp B).comp ι.symm.toLinearMap
  have hℓ₀ (f : V ds) : ℓ₀ (ι f) = B f 1 := by
    change B (ι.symm (ι f)) 1 = B f 1
    rw [LinearEquiv.symm_apply_apply]
  have hbound : ∀ w : LinearMap.range Φ, ‖ℓ₀ w‖ ≤ Df * Cd * ∑ Xs ∈ Ws,
      ‖iteratedLieDerivative I (R ds) Xs (w : Langlands.Archimedean.smoothVectors I (R ds))‖ := by
    intro w
    obtain ⟨f, rfl⟩ := ι.surjective w
    let f₀ : S ds := ⟨f.val, f.property.1⟩
    have hw (Xs : List M) : iteratedLieDerivative I (R ds) Xs
        ((ι f : LinearMap.range Φ) : Langlands.Archimedean.smoothVectors I (R ds)) =
          derivativeCLM I (R ds) Xs (derivativeEquiv ds f₀) := by
      rw [derivativeCLM_apply]
      rfl
    simp only [hw, hℓ₀]
    have hWord : WordBound J (f : G → ℂ)
        (∑ Xs ∈ Ws, ‖derivativeCLM I (R ds) Xs (derivativeEquiv ds f₀)‖) := by
      intro w hw x
      rw [← derivativeCLM_compactEval ds (word w) f₀ x]
      refine ((derivativeCLM I (R ds) (word w) (derivativeEquiv ds f₀)).val.norm_coe_le_norm
        x).trans ?_
      exact Finset.single_le_sum
        (f := fun Xs => ‖derivativeCLM I (R ds) Xs (derivativeEquiv ds f₀)‖)
        (fun _ _ => norm_nonneg _)
        (Finset.mem_image_of_mem word ((Set.Finite.mem_toFinset _).mpr hw))
    calc
      ‖B f 1‖ ≤ Df * (Cd * ∑ Xs ∈ Ws, ‖derivativeCLM I (R ds) Xs (derivativeEquiv ds f₀)‖) :=
        hOrder f _ (hDiff f _ hWord)
      _ = _ := by ring
  obtain ⟨L₀, hL₀, -, hcont⟩ := exists_extension_of_word_bound I (R ds) (LinearMap.range Φ) ℓ₀
    Ws (Df * Cd) (mul_nonneg hDf hCd) hbound
  refine ⟨⟨L₀.comp (toSmooth I (R ds)).toLinearMap,
    continuous_of_isContinuousOnSmoothVectors I (R ds) L₀ hcont⟩, fun f => ?_⟩
  change L₀ (toSmooth I (R ds) (compactFiniteEquiv ds f).val) = B f 1
  rw [← hℓ₀ f, ← hL₀ (ι f)]
  rfl

/-- A continuous functional agreeing with an exact Whittaker intertwiner at the identity on
compact-finite vectors agrees with it after every right translation. -/
theorem translate_identity (ds : List RealBlock) (a : ℝˣ) (B : (V ds) →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r ds a B) (L : (D ds) →L[ℂ] ℂ)
    (hL : ∀ f : V ds, L (compactFiniteEquiv ds f).val = B f 1) (f : V ds) (g : G) :
    L (act ds g (compactFiniteEquiv ds f).val) = B f g := by
  have hR := isContinuousRepresentation (n := r + 1) ds
  let v := (compactFiniteEquiv ds f).val
  have hOrbit : Continuous fun h : G => L (act ds h v) :=
    continuous_apply_representation (R ds) hR L v
  have hBf : Continuous (B f) := (hB.2.1 f).continuous
  let F : C(U, ℂ) :=
    ⟨fun k => L (act ds (Unitary.toUnits k * g) v) - B f (Unitary.toUnits k * g),
      (hOrbit.comp (continuous_unitary_toUnits.mul continuous_const)).sub
        (hBf.comp (continuous_unitary_toUnits.mul continuous_const))⟩
  have hF : ∀ φ ∈ polynomialStar (r + 1), ∫ k, φ k * F k ∂orthogonalHaar r = 0 := by
    intro φ hφ
    let κ := compactWeight φ
    obtain ⟨p, hp, hBp⟩ := realExactCompactProjection r ds a (haarK (r + 1)) inferInstance κ
      (finiteDimensional_compactWeight hφ) B hB f g
    have hA := apply_compactSmoothAverage (R ds) hR (haarK (r + 1)) (compactTranslate g) κ v L
    rw [compactSmoothAverage_eq ds κ f p g hp, hL, hBp] at hA
    have hcF : Continuous fun k : U => φ k * F k := φ.continuous.mul F.continuous
    rw [orthogonalHaar, integral_map
      (continuous_unitaryCompactMatrix ℝ (r + 1)).measurable.aemeasurable
      hcF.aestronglyMeasurable]
    have hpt (k : Kc) : φ (unitaryCompactMatrix ℝ (r + 1) k) *
        F (unitaryCompactMatrix ℝ (r + 1) k) =
          κ k • L (act ds (compactTranslate g k) v) - κ k * B f (1 * k.val * g) := by
      change φ (unitaryCompactMatrix ℝ (r + 1) k) *
          (L (act ds (Unitary.toUnits (unitaryCompactMatrix ℝ (r + 1) k) * g) v) -
            B f (Unitary.toUnits (unitaryCompactMatrix ℝ (r + 1) k) * g)) =
        φ (unitaryCompactMatrix ℝ (r + 1) k) * L (act ds (k.val * g) v) -
          φ (unitaryCompactMatrix ℝ (r + 1) k) * B f (1 * k.val * g)
      rw [toUnits_unitaryCompactMatrix, one_mul, mul_sub]
    simp_rw [hpt]
    have hc₁ : Continuous fun k : Kc => κ k • L (act ds (compactTranslate g k) v) :=
      κ.continuous.smul (hOrbit.comp (compactTranslate g).continuous)
    have hc₂ : Continuous fun k : Kc => κ k * B f (1 * k.val * g) :=
      κ.continuous.mul (hBf.comp ((continuous_const.mul continuous_subtype_val).mul
        continuous_const))
    rw [integral_sub (hc₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hc₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), ← hA, sub_self]
  have hz := congrArg (fun F : C(U, ℂ) => F 1)
    (eq_zero_of_integral_polynomial_mul_eq_zero (orthogonalHaar r) F hF)
  change L (act ds (Unitary.toUnits (1 : U) * g) v) - B f (Unitary.toUnits (1 : U) * g) = 0
    at hz
  rw [map_one, one_mul, sub_eq_zero] at hz
  exact hz

/-- The translated identity evaluation of an exact Whittaker intertwiner is Whittaker covariant
on all genuine smooth vectors. -/
theorem isWhittakerStandardEvaluation_of_identity (ds : List RealBlock) (a : ℝˣ)
    (B : (V ds) →ₗ[ℂ] (G → ℂ)) (hB : IsRealWhittakerIntertwiner r ds a B) (L : (D ds) →L[ℂ] ℂ)
    (hL : ∀ f : V ds, L (compactFiniteEquiv ds f).val = B f 1) :
    IsWhittakerStandardEvaluation ds a B L := by
  have hTr := translate_identity ds a B hB L hL
  refine ⟨hTr, fun u w => ?_⟩
  have hd := denseRange_compactFiniteEquiv (r := r) ds
  let Tu := SmoothAction.derivativeAction I (R ds) u.val
  have hLeft : Continuous (fun z => L (Tu z)) := L.continuous.comp Tu.continuous
  have hRight : Continuous (fun z => realWhittakerCharacter a u.val * L z) :=
    continuous_const.mul L.continuous
  have he := hd.equalizer hLeft hRight (funext fun f => by
    change L (act ds u.val (compactFiniteEquiv ds f).val) =
      realWhittakerCharacter a u.val * L (compactFiniteEquiv ds f).val
    rw [hTr, hL]
    simpa only [mul_one] using hB.1 f u.val u.property 1)
  exact congrFun he w

/-- For a real character list, each specified real Whittaker intertwiner is evaluated by one
continuous functional on the genuine smooth vectors. -/
theorem exists_standardEvaluation (cs : List RealCharacterData) (a : ℝˣ)
    (B : (V (cs.map RealBlock.character)) →ₗ[ℂ] (G → ℂ))
    (hB : IsRealWhittakerIntertwiner r (cs.map RealBlock.character) a B) :
    ∃ L : (D (cs.map RealBlock.character)) →L[ℂ] ℂ,
      IsWhittakerStandardEvaluation (cs.map RealBlock.character) a B L := by
  obtain ⟨J, Df, hDf, hOrder⟩ := realWhittakerFiniteOrder r cs a B hB
  obtain ⟨L, hL⟩ := exists_continuous_identityEvaluation _ B J Df hDf hOrder
  exact ⟨L, isWhittakerStandardEvaluation_of_identity _ a B hB L hL⟩

/-- For every real character list, every specified real Whittaker intertwiner of the
compact-finite standard module is the translated evaluation of one continuous Whittaker functional
on the genuine smooth vectors of the compact Banach completion. -/
def RealExactStandardEvaluationStatement : Prop :=
  ∀ (r : ℕ) (cs : List RealCharacterData) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (r + 1) (cs.map RealBlock.character) →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealWhittakerIntertwiner r (cs.map RealBlock.character) a B →
    ∃ L : DerivativeSmoothVectors (matrixModel ℝ (r + 1))
        (RealStandardCompactBanach.representation (n := r + 1)
          (cs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (cs.map RealBlock.character) a B L

theorem realExactStandardEvaluation : RealExactStandardEvaluationStatement :=
  fun r cs a B hB => exists_standardEvaluation (r := r) cs a B hB

end Langlands.Global.RankinSelbergGlobal.RealExactStandardEvaluation
