import Langlands.Global.RankinSelberg.RealBlockSmoothExtension
import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealInductionStagesDerivative
import Langlands.Representation.Archimedean.RealStandardCompactDerivativeFormula
import Langlands.Representation.Archimedean.SmoothCasselmanWallachBound
import Langlands.Representation.Archimedean.SmoothRealGroupIntertwining

/-! # Smooth right inverses for real standard tail quotients -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealBlockFrobeniusMap RealBlockMultiplier
open SmoothCasselmanWallachBound (gkWord operatorWord map_gkWord continuous_operatorWord
  operatorWord_zero derivativeCLM_nil_operatorWord)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

variable {r : ℕ}

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "F" ds:max => smoothKFinite ℝ (r + 1) (R ds)
local notation:max "L" ds:max => realStandardLie (r + 1) ds

private def compactIncl (ds : List RealBlock) (f : V ds) : D ds :=
  (compactFiniteEquiv ds f).val

/-- Compact equivariance of a block multiplier gives commutation with right
skew derivatives by differentiating the compact one-parameter subgroup. -/
theorem blockFrobMap_skewDerivative {ds es : List RealBlock} {p : ℕ} {ε : ℤ}
    {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (X : M) (hX : Xᵀ = -X) (f : V ds) :
    blockFrobMap h (L ds (1 ⊗ₜ[ℝ] X) f) = L es (1 ⊗ₜ[ℝ] X) (blockFrobMap h f) := by
  apply Subtype.ext
  funext g
  let ℓ : V es →ₗ[ℂ] ℂ := (LinearMap.proj g).comp (V es).subtype
  let γ := InductionStages.expCurve X hX
  have hs := (isRealGKModule_realStandardModule (r + 1) ds).2.2.1 γ X
    (InductionStages.expCurve_zero X hX) (InductionStages.hasDerivAt_expCurve X hX) f
    (ℓ.comp (blockFrobMap h))
  have ht := (isRealGKModule_realStandardModule (r + 1) es).2.2.1 γ X
    (InductionStages.expCurve_zero X hX) (InductionStages.hasDerivAt_expCurve X hX)
    (blockFrobMap h f) ℓ
  have he (t : ℝ) : (ℓ.comp (blockFrobMap h)) (realStandardRep (r + 1) ds (γ t) f) =
      ℓ (realStandardRep (r + 1) es (γ t) (blockFrobMap h f)) :=
    congrArg ℓ (blockFrobMap_rightTranslation h (γ t) f)
  rw [funext he] at hs
  exact hs.unique ht

private theorem compactIncl_algebraicWord (ds : List RealBlock) (Xs : List M) (f : V ds) :
    compactIncl ds (gkWord (L ds) Xs f) = operatorWord (R ds) Xs (compactIncl ds f) :=
  map_gkWord (L ds) (R ds) ((F ds).subtype.comp (compactFiniteEquiv ds).toLinearMap)
    (isSmoothGKIntertwiner_compactFiniteEquiv ds).2 Xs f

private theorem blockFrobMap_algebraicWord_skew {ds es : List RealBlock} {p : ℕ} {ε : ℤ}
    {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (Xs : List M) (hXs : ∀ Y ∈ Xs, Yᵀ = -Y) (f : V ds) :
    blockFrobMap h (gkWord (L ds) Xs f) = gkWord (L es) Xs (blockFrobMap h f) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change blockFrobMap h (L ds (1 ⊗ₜ[ℝ] X) (gkWord (L ds) Xs f)) =
      L es (1 ⊗ₜ[ℝ] X) (gkWord (L es) Xs (blockFrobMap h f))
    rw [blockFrobMap_skewDerivative h X (hXs X List.mem_cons_self)]
    rw [ih (fun Y hY => hXs Y (List.mem_cons_of_mem X hY))]

set_option maxHeartbeats 650000 in
/-- Polynomial size of a block multiplier gives a continuous extension on genuine
smooth vectors, using compact directions to control its target word seminorms. -/
theorem exists_continuous_blockFrobMap_compact {ds es : List RealBlock} {p : ℕ} {ε : ℤ}
    {σ : ℂ} {μ : ℤ → ℂ} (h : IsBlockFrobData (r + 1) ds es p ε σ μ)
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (hμ : ∀ j, ‖μ j‖ ≤ C * (max 1 |(j : ℝ)|) ^ d) :
    ∃ T : D ds →L[ℂ] D es, ∀ f, T (compactIncl ds f) = compactIncl es (blockFrobMap h f) := by
  obtain ⟨A, hA, hA₀, hbound⟩ := exists_continuous_norm_bound_blockFrobMap h d hC hμ
  let t : F ds →ₗ[ℂ] D es := (F es).subtype.comp ((compactFiniteEquiv es).toLinearMap.comp
    ((blockFrobMap h).comp (compactFiniteEquiv ds).symm.toLinearMap))
  have ht (f : V ds) : t (compactFiniteEquiv ds f) = compactIncl es (blockFrobMap h f) := by
    simp [t, compactIncl]
  have htc : Continuous t := by
    apply (isEmbedding_derivativeCoordinates I (R es)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro Xs
    let l := (derivativeCLM I (R es) Xs).toLinearMap.comp t
    change Continuous l
    apply continuous_of_tendsto_nhds_zero l
    obtain ⟨T, B, hB, hT, hnorm⟩ := RealStandardCompactDifferential.exists_compactWordBound es Xs
    let Q (x : F ds) := B * ∑ w ∈ T, A (operatorWord (R ds) w x.val)
    have hQc : Continuous Q := continuous_const.mul (continuous_finsetSum T fun w _ =>
      hA.comp ((continuous_operatorWord (R ds) w).comp continuous_subtype_val))
    have hQ₀ : Q 0 = 0 := by simp [Q, operatorWord_zero, hA₀]
    refine squeeze_zero_norm (fun x => ?_) (hQ₀ ▸ hQc.continuousAt.tendsto)
    obtain ⟨f, rfl⟩ := (compactFiniteEquiv ds).surjective x
    change ‖derivativeCLM I (R es) Xs (t (compactFiniteEquiv ds f))‖ ≤ Q (compactFiniteEquiv ds f)
    rw [ht]
    have h1 := hnorm (toSmooth I (R es) (compactIncl es (blockFrobMap h f)))
    simp only [← derivativeCLM_apply] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w hw => ?_) hB)
    rw [← derivativeCLM_nil_operatorWord, ← compactIncl_algebraicWord,
      ← blockFrobMap_algebraicWord_skew h w (hT w hw)]
    exact (hbound (gkWord (L ds) w f)).trans_eq
      (congrArg A (compactIncl_algebraicWord ds w f))
  let t₀ : F ds →L[ℂ] D es := ⟨t, htc⟩
  let e : F ds →L[ℂ] D ds := ⟨(F ds).subtype, continuous_subtype_val⟩
  let : CompleteSpace (D es) := completeSpace_of_isContinuousRepresentation_units
    (R es) (isContinuousRepresentation es)
  let : IsUniformAddGroup (F ds) := (F ds).toAddSubgroup.isUniformAddGroup
  have he : DenseRange e := by
    apply (denseRange_compactFiniteEquiv (r := r) ds).mono
    rintro _ ⟨f, hf⟩
    exact ⟨compactFiniteEquiv ds f, hf⟩
  exact ⟨t₀.extend e, fun f =>
    (t₀.extend_eq he isUniformEmbedding_subtype_val.isUniformInducing
      (compactFiniteEquiv ds f)).trans (ht f)⟩

/-- Reciprocals of the signed binomial tail symbol are bounded by one. -/
theorem norm_tailMultiplier_inv_le (m : ℕ) (ε : ℤ) {σ : ℂ} (hσ : ‖σ‖ = 1) (j : ℤ) :
    ‖(tailMultiplier m ε σ j)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have h : ‖tailMultiplier m ε σ j‖ =
      ((j.natAbs / 2 + (m - 1 + ε.toNat) / 2).choose m : ℝ) := by
    by_cases hj : 0 ≤ j
    · rw [tailMultiplier, extend_of_nonneg hj, tailSeq, Complex.norm_natCast]
    · rw [tailMultiplier, extend_of_neg (lt_of_not_ge hj), norm_mul, hσ, one_mul,
        tailSeq, Complex.norm_natCast]
  rw [h]
  let k := (j.natAbs / 2 + (m - 1 + ε.toNat) / 2).choose m
  change (k : ℝ)⁻¹ ≤ 1
  by_cases hk : k = 0
  · simp [hk]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk))

open RealInducedCharacter RealCharacterPair in
/-- The smooth extension of an ascending rank-two tail quotient has a continuous
linear right inverse extending the algebraic reciprocal Fourier multiplier. -/
def RealBlockSmoothTailSectionStatement : Prop :=
  ∀ (r : ℕ) (pre post : List RealBlock) (d : ComplexCharacterData) (sa sb : Fin 2)
    (hr : realRank (pre ++ [RealBlock.induced d] ++ post) = r + 1)
    (hl : 0 < d.weight.natAbs) (hp : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2),
    let src := pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post
    let tgt := pre ++ [RealBlock.induced d] ++ post
    let J := matrixModel ℝ (r + 1)
    let Rsrc := representation (n := r + 1) src
    let Rtgt := representation (n := r + 1) tgt
    ∃ (Q : DerivativeSmoothVectors J Rsrc →L[ℂ] DerivativeSmoothVectors J Rtgt)
      (S : DerivativeSmoothVectors J Rtgt →L[ℂ] DerivativeSmoothVectors J Rsrc),
      (∀ v, Q (S v) = v) ∧
      (∀ g v, Q (DerivativeSmoothVectors.representation J Rsrc g v) =
        DerivativeSmoothVectors.representation J Rtgt g (Q v)) ∧
      (∀ f, Q ((compactFiniteEquiv src) f).val =
        ((compactFiniteEquiv tgt) (blockFrobMap (data_tail hr hl hp) f)).val) ∧
      (∀ f, S ((compactFiniteEquiv tgt) f).val =
        ((compactFiniteEquiv src) (blockFrobMap (data_tailInv hr hl hp) f)).val)

open RealInducedCharacter RealCharacterPair in
theorem realBlockSmoothTailSection : RealBlockSmoothTailSectionStatement := by
  intro r pre post d sa sb hr hl hp src tgt J Rsrc Rtgt
  let C := ((d.weight.natAbs + (pairParity (cb d sb) (ca d sa)).toNat + 1 : ℕ) : ℝ) ^
    d.weight.natAbs
  have hs : ‖((-1 : ℂ) ^ sa.val)‖ = 1 := by simp
  obtain ⟨Q, hQ, hLie, hK⟩ := exists_continuous_blockFrobMap (data_tail hr hl hp)
    (isRecurrent_tail hl hp) d.weight.natAbs (C := C) (by dsimp [C]; positivity)
    (RealBlockFourierDecay.norm_tailMultiplier_le _ _ hs)
  obtain ⟨S, hS⟩ := exists_continuous_blockFrobMap_compact (data_tailInv hr hl hp) 0
    (C := 1) zero_le_one (fun j => by simpa using norm_tailMultiplier_inv_le _ _ hs j)
  refine ⟨Q, S, ?_, map_representation_real_of_compact_and_lie _ _
    (isContinuousRepresentation _) (isContinuousRepresentation _) Q hLie hK, hQ, hS⟩
  have h := (denseRange_compactFiniteEquiv (r := r) tgt).equalizer
    (Q.continuous.comp S.continuous) continuous_id (funext fun f => by
      change Q (S (compactIncl tgt f)) = compactIncl tgt f
      rw [hS]
      exact (hQ (blockFrobMap (data_tailInv hr hl hp) f)).trans
        (congrArg (compactIncl tgt) (tail_tailInv hr hl hp f)))
  exact congrFun h

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
