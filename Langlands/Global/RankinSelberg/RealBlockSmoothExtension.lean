import Langlands.Global.RankinSelberg.RealSmoothWhittakerEvaluation
import Langlands.Representation.Archimedean.RealBlockFourierDecay
import Langlands.Representation.Archimedean.SmoothDerivativeCompleteness
import Langlands.Representation.Archimedean.SmoothModerateGrowth
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend

/-! # Smooth extension of bounded real block Fourier multipliers -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealBlockFourierDecay RealBlockFrobeniusMap RealBlockMultiplier

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "F" ds:max => smoothKFinite ℝ (r + 1) (R ds)
local notation:max "coord" ds:max => derivativeCoordinates I (R ds)
local notation:max "L" ds:max => realStandardLie (r + 1) ds
local notation:max "dR" ds:max => operator I (R ds)

private def compactFiniteIncl (ds : List RealBlock) (f : V ds) : D ds :=
  (compactFiniteEquiv ds f).val

private def algebraicWord (ds : List RealBlock) (Xs : List M) (f : V ds) : V ds :=
  Xs.foldr (fun X v => L ds (1 ⊗ₜ[ℝ] X) v) f

private def smoothWord (ds : List RealBlock) (Xs : List M) (f : D ds) : D ds :=
  Xs.foldr (fun X v => dR ds X v) f

private theorem continuous_smoothWord (ds : List RealBlock) (Xs : List M) :
    Continuous (smoothWord ds Xs) := by
  induction Xs with
  | nil => exact continuous_id
  | cons X Xs ih => exact (continuous_operator I (R ds) X).comp ih

private theorem smoothWord_zero (ds : List RealBlock) (Xs : List M) : smoothWord ds Xs 0 = 0 := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change dR ds X (smoothWord ds Xs 0) = 0
    rw [ih, map_zero]

private theorem compactFiniteEquiv_algebraicWord (ds : List RealBlock) (Xs : List M) (f : V ds) :
    compactFiniteIncl ds (algebraicWord ds Xs f) = smoothWord ds Xs (compactFiniteIncl ds f) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change compactFiniteIncl ds (L ds (1 ⊗ₜ[ℝ] X) (algebraicWord ds Xs f)) =
      dR ds X (smoothWord ds Xs (compactFiniteIncl ds f))
    exact ((isSmoothGKIntertwiner_compactFiniteEquiv ds).2 X (algebraicWord ds Xs f)).trans
      (congrArg (dR ds X) ih)

private theorem coords_smoothWord (ds : List RealBlock) (pre post : List M) (v : D ds) :
    coord ds (smoothWord ds post v) pre = coord ds v (pre ++ post) := by
  induction post generalizing pre with
  | nil => simp only [smoothWord, List.foldr_nil, List.append_nil]
  | cons X post ih =>
    change coord ds (dR ds X (smoothWord ds post v)) pre = _
    rw [derivativeCoordinates_operator, ih, List.append_assoc]
    rfl

private theorem compactFiniteEquiv_coordinate_eval (ds : List RealBlock) (f : V ds) (k : U) :
    (coord ds (compactFiniteIncl ds f) []).val k = f.val (Unitary.toUnits k) := by
  rw [compactFiniteIncl, derivativeCoordinates_apply, iteratedLieDerivative_nil, compactFiniteEquiv_val,
    toSmooth_derivativeEquiv, embed_val, compactRestriction_apply]

private theorem norm_algebraicWord_eval_le (ds : List RealBlock) (Xs : List M)
    (f : V ds) {k : G} (hk : k ∈ K) :
    ‖(algebraicWord ds Xs f).val k‖ ≤ wordSeminormFamily I (R ds) Xs (compactFiniteIncl ds f) := by
  let u : U := ⟨k.val, hk⟩
  have hu : Unitary.toUnits u = k := Units.ext rfl
  have h := compactFiniteEquiv_coordinate_eval ds (algebraicWord ds Xs f) u
  rw [hu, compactFiniteEquiv_algebraicWord, coords_smoothWord, List.nil_append] at h
  rw [← h, wordSeminormFamily_apply, ← derivativeCoordinates_apply]
  exact ContinuousMap.norm_coe_le_norm _ _

private theorem algebraicWord_replicate (ds : List RealBlock) (m : ℕ) (X : M) (f : V ds) :
    (algebraicWord ds (List.replicate m X) f).val =
      (rightDerivative I X)^[m] f.val := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply']
    change (L ds (1 ⊗ₜ[ℝ] X) (algebraicWord ds (List.replicate m X) f)).val = _
    rw [realStandardLie_one_tmul_apply_coe, ih]

private theorem norm_emptyCoord_le (ds : List RealBlock) (f : V ds) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k ∈ K, ‖f.val k‖ ≤ C) : ‖coord ds (compactFiniteIncl ds f) []‖ ≤ C := by
  apply (ContinuousMap.norm_le _ hC).mpr
  intro k
  change ‖(coord ds (compactFiniteIncl ds f) []).val k‖ ≤ C
  rw [compactFiniteEquiv_coordinate_eval]
  exact hf _ k.property

variable {ds es : List RealBlock} {p : ℕ} {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}

/-- The empty word of a polynomially bounded block multiplier is controlled by a
continuous expression in two fixed derivative orders of the input. -/
theorem exists_continuous_norm_bound_blockFrobMap
    (h : IsBlockFrobData (r + 1) ds es p ε σ μ) (d : ℕ) {C : ℝ}
    (hC : 0 ≤ C) (hμ : ∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) :
    ∃ A : D ds → ℝ, Continuous A ∧ A 0 = 0 ∧
      ∀ f : V ds, ‖coord es (compactFiniteIncl es (blockFrobMap h f)) []‖ ≤ A (compactFiniteIncl ds f) := by
  obtain ⟨B, hB, hb⟩ := realBlockFourierDecay (r + 1) p d ds es ε σ μ h C hC hμ
  have hc : Continuous (rotationDirection (r + 1) p : G → M) :=
    (Units.continuous_coe_inv.mul continuous_const).mul Units.continuous_val
  have hK : IsCompact (unitaryCompact ℝ (r + 1) : Set G) :=
    isCompact_iff_compactSpace.mpr (RealPrincipalSeriesDuality.compactSpace_unitaryCompact _)
  obtain ⟨J, hJ⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  let b := Module.finBasis ℝ M
  let Q (v : D ds) := wordSeminormFamily I (R ds) [] v +
    J ^ (d + 2) * wordOrderSeminorm (R ds) b (d + 2) v
  have hJ₀ : 0 ≤ J := (norm_nonneg _).trans (hJ 1 (Subgroup.one_mem _))
  have hQ₀ (v : D ds) : 0 ≤ Q v := by dsimp only [Q]; positivity
  have hQ₁ (f : V ds) : wordSeminormFamily I (R ds) [] (compactFiniteIncl ds f) ≤ Q (compactFiniteIncl ds f) := by
    dsimp only [Q]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hJ₀ _) (apply_nonneg _ _))
  have hQc : Continuous Q := (derivativeCLM I (R ds) []).continuous.norm.add
    (continuous_const.mul (continuous_wordOrderSeminorm (R ds) b (d + 2)))
  refine ⟨fun v => B * Q v, continuous_const.mul hQc, by simp [Q], fun f => ?_⟩
  apply norm_emptyCoord_le es _ (mul_nonneg hB (hQ₀ _))
  intro g hg
  refine hb f g hg _ (fun k hk => (norm_algebraicWord_eval_le ds [] f hk).trans (hQ₁ f)) ?_
  intro k hk
  let X := rotationDirection (r + 1) p g
  have h := norm_algebraicWord_eval_le ds (List.replicate (d + 2) X) f hk
  rw [algebraicWord_replicate] at h
  refine h.trans ((wordSeminormFamily_le_wordOrderSeminorm (R ds) b _ _).trans ?_)
  rw [List.map_replicate, List.prod_replicate, List.length_replicate]
  have hpow : ‖X‖ ^ (d + 2) ≤ J ^ (d + 2) := pow_le_pow_left₀ (norm_nonneg _) (hJ g hg) _
  exact (mul_le_mul_of_nonneg_right hpow (apply_nonneg _ _)).trans
    (le_add_of_nonneg_left (apply_nonneg _ _))

private theorem blockFrobMap_algebraicWord (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p -
      GramFormula.realPositionExponent ds (p + 1) + 1) ε μ) (Xs : List M) (f : V ds) :
    blockFrobMap h (algebraicWord ds Xs f) = algebraicWord es Xs (blockFrobMap h f) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change blockFrobMap h (L ds (1 ⊗ₜ[ℝ] X) (algebraicWord ds Xs f)) =
      L es (1 ⊗ₜ[ℝ] X) (algebraicWord es Xs (blockFrobMap h f))
    rw [blockFrobMap_rightDerivative h hrec, ih]

set_option maxHeartbeats 650000 in
/-- A recurrent polynomially bounded multiplier extends continuously to the
full genuine derivative carriers and commutes with every derived operator. -/
theorem exists_continuous_blockFrobMap
    (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (hrec : IsRecurrent (GramFormula.realPositionExponent ds p -
      GramFormula.realPositionExponent ds (p + 1) + 1) ε μ)
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) :
    ∃ T : D ds →L[ℂ] D es,
      (∀ f, T (compactFiniteIncl ds f) = compactFiniteIncl es (blockFrobMap h f)) ∧
      (∀ X v, T (dR ds X v) = dR es X (T v)) ∧
      (∀ (k : U) v,
        T (DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k) v) =
          DerivativeSmoothVectors.representation I (R es) (Unitary.toUnits k) (T v)) := by
  obtain ⟨A, hA, hA₀, hbound⟩ := exists_continuous_norm_bound_blockFrobMap h d hC hμ
  let t : F ds →ₗ[ℂ] D es := (F es).subtype.comp ((compactFiniteEquiv es).toLinearMap.comp
    ((blockFrobMap h).comp (compactFiniteEquiv ds).symm.toLinearMap))
  have ht (f : V ds) : t (compactFiniteEquiv ds f) = compactFiniteIncl es (blockFrobMap h f) := by
    simp [t, compactFiniteIncl]
  have htc : Continuous t := by
    apply (isEmbedding_derivativeCoordinates I (R es)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro Xs
    let T := (derivativeCLM I (R es) Xs).toLinearMap.comp t
    change Continuous T
    apply continuous_of_tendsto_nhds_zero T
    have hQ : Continuous (fun x : F ds => A (smoothWord ds Xs x.val)) :=
      hA.comp ((continuous_smoothWord ds Xs).comp continuous_subtype_val)
    have hQ₀ : A (smoothWord ds Xs (0 : F ds).val) = 0 := by
      rw [show (0 : F ds).val = 0 from rfl, smoothWord_zero, hA₀]
    refine squeeze_zero_norm (fun x => ?_) (hQ₀ ▸ hQ.continuousAt.tendsto)
    obtain ⟨f, rfl⟩ := (compactFiniteEquiv ds).surjective x
    change ‖coord es (t (compactFiniteEquiv ds f)) Xs‖ ≤ A (smoothWord ds Xs (compactFiniteIncl ds f))
    rw [ht, ← List.nil_append Xs, ← coords_smoothWord, ← compactFiniteEquiv_algebraicWord,
      ← blockFrobMap_algebraicWord h hrec, ← compactFiniteEquiv_algebraicWord]
    exact hbound (algebraicWord ds Xs f)
  let t₀ : F ds →L[ℂ] D es := ⟨t, htc⟩
  let e : F ds →L[ℂ] D ds := ⟨(F ds).subtype, continuous_subtype_val⟩
  let : CompleteSpace (D es) := completeSpace_of_isContinuousRepresentation_units
    (R es) (isContinuousRepresentation es)
  let : IsUniformAddGroup (F ds) := (F ds).toAddSubgroup.isUniformAddGroup
  have hd := denseRange_compactFiniteEquiv (r := r) ds
  have he : DenseRange e := by
    apply hd.mono
    rintro _ ⟨f, hf⟩
    exact ⟨compactFiniteEquiv ds f, hf⟩
  let T := t₀.extend e
  have hT (f : V ds) : T (compactFiniteIncl ds f) = compactFiniteIncl es (blockFrobMap h f) :=
    (t₀.extend_eq he isUniformEmbedding_subtype_val.isUniformInducing
      (compactFiniteEquiv ds f)).trans (ht f)
  refine ⟨T, hT, ?_, ?_⟩
  · intro X v
    have h := hd.equalizer (T.continuous.comp (continuous_operator I (R ds) X))
      ((continuous_operator I (R es) X).comp T.continuous) (funext fun f => by
        change T (dR ds X (compactFiniteIncl ds f)) = dR es X (T (compactFiniteIncl ds f))
        have hX : compactFiniteIncl ds (L ds (1 ⊗ₜ[ℝ] X) f) =
            dR ds X (compactFiniteIncl ds f) := (isSmoothGKIntertwiner_compactFiniteEquiv ds).2 X f
        rw [← hX, hT, hT, blockFrobMap_rightDerivative h hrec]
        exact (isSmoothGKIntertwiner_compactFiniteEquiv es).2 X (blockFrobMap h f))
    exact congrFun h v
  · intro k v
    let R₁ := SmoothAction.derivativeAction I (R ds) (Unitary.toUnits k)
    let R₂ := SmoothAction.derivativeAction I (R es) (Unitary.toUnits k)
    have h := hd.equalizer (T.continuous.comp R₁.continuous)
      (R₂.continuous.comp T.continuous) (funext fun f => by
        change T (DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k) (compactFiniteIncl ds f)) =
          DerivativeSmoothVectors.representation I (R es) (Unitary.toUnits k) (T (compactFiniteIncl ds f))
        have hk : compactFiniteIncl ds (realStandardRep (r + 1) ds k f) =
            DerivativeSmoothVectors.representation I (R ds) (Unitary.toUnits k) (compactFiniteIncl ds f) :=
          (isSmoothGKIntertwiner_compactFiniteEquiv ds).1 k f
        rw [← hk, hT, hT, blockFrobMap_rightTranslation h k]
        exact (isSmoothGKIntertwiner_compactFiniteEquiv es).1 k (blockFrobMap h f))
    exact congrFun h v

/-- A block Frobenius map with a polynomially bounded recurrent symbol has
a continuous compact- and Lie-equivariant extension in the genuine smooth topology. -/
def RealBlockSmoothExtensionStatement : Prop :=
  ∀ (r p d : ℕ) (ds es : List RealBlock) (ε : ℤ) (σ : ℂ) (μ : ℤ → ℂ)
    (h : IsBlockFrobData (r + 1) ds es p ε σ μ),
    IsRecurrent (GramFormula.realPositionExponent ds p -
      GramFormula.realPositionExponent ds (p + 1) + 1) ε μ →
    ∀ C : ℝ, 0 ≤ C → (∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) →
    let J := matrixModel ℝ (r + 1)
    let R₁ := representation (n := r + 1) ds
    let R₂ := representation (n := r + 1) es
    ∃ T : DerivativeSmoothVectors J R₁ →L[ℂ] DerivativeSmoothVectors J R₂,
      (∀ f, T (compactFiniteEquiv ds f).val = (compactFiniteEquiv es (blockFrobMap h f)).val) ∧
      (∀ X v, T (operator J R₁ X v) = operator J R₂ X (T v)) ∧
      (∀ (k : Matrix.unitaryGroup (Fin (r + 1)) ℝ) v,
        T (DerivativeSmoothVectors.representation J R₁ (Unitary.toUnits k) v) =
          DerivativeSmoothVectors.representation J R₂ (Unitary.toUnits k) (T v))

theorem realBlockSmoothExtension : RealBlockSmoothExtensionStatement :=
  fun _ _ d _ _ _ _ _ h hrec _ hC hμ => exists_continuous_blockFrobMap h hrec d hC hμ

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
