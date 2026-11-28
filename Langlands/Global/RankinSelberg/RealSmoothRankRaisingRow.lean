import Langlands.Global.RankinSelberg.RealRankRaisingSmoothFactorization

/-! # The real smooth rank-raising identity with bottom-row tests -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal ENNReal SchwartzMap ContDiff Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)
open Langlands.Archimedean.DerivativeSmoothVectors
open ArchimedeanLocal
open ArchimedeanRealPairIdentity (sigmaFinite_rect)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (lowerTriangularSubgroup n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (lowerTriangularSubgroup n ℝ) := ⟨rfl⟩
private local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r ℝ) := borel _
private local instance (r : ℕ) : BorelSpace (LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Q" => fun r => LeftUnipotentQuotient r ℝ
local notation "B" => lowerTriangularSubgroup 1 ℝ
local notation "X" => fun r => Matrix (Fin 1) (Fin (r + 1)) ℝ
local notation "P" => fun r => X r × B
local notation "W" => fun r => X r × ℝ
local notation "M" => fun r => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℝ
local notation "I" => fun r => matrixModel ℝ (r + 1 + 1)
local notation "chart" => fun r => lowerBlockQuotientChart (a := r + 1) (d := 1) (R := ℝ)

/-- The first entries of the last row and its last entry, in the coordinates of
rank-raising Schwartz tests. -/
def splitBottomRow {r : ℕ} (g : G (r + 1)) : W r :=
  (fun _ i => Langlands.RankinSelberg.lastRow g i.castSucc,
    Langlands.RankinSelberg.lastRow g (Fin.last (r + 1)))

private theorem continuous_splitBottomRow {r : ℕ} : Continuous (splitBottomRow (r := r)) := by
  have h : ∀ i j : Fin (r + 1 + 1), Continuous (fun g : G (r + 1) => g.val i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  exact (continuous_matrix fun (_ : Fin 1) (i : Fin (r + 1)) =>
    h (Fin.last (r + 1)) i.castSucc).prodMk (h _ _)

private theorem splitBottomRow_leftUnipotent {r : ℕ} (u : N (r + 1)) (g : G (r + 1)) :
    splitBottomRow (u.val * g) = splitBottomRow g := by
  simp only [splitBottomRow, Langlands.RankinSelberg.lastRow_unipotent_mul]

private theorem splitBottomRow_lowerBlockPair {r : ℕ} (g : G r) (y : P r) :
    splitBottomRow (lowerBlockPair g y.1 y.2) = (y.1, y.2.val.val.det) := by
  apply Prod.ext
  · ext i j
    have hi : Fin.last (r + 1) = i.natAdd (r + 1) := by fin_cases i; rfl
    change (lowerBlockPair g y.1 y.2) (Fin.last (r + 1)) j.castSucc = y.1 i j
    rw [hi]
    exact lowerBlockPair_21 g y.1 y.2 i j
  · change (lowerBlockPair g y.1 y.2) (Fin.last (r + 1)) (Fin.last (r + 1)) = y.2.val.val.det
    have hi : Fin.last (r + 1) = (0 : Fin 1).natAdd (r + 1) := rfl
    rw [hi, lowerBlockPair_22, Matrix.det_fin_one]

private theorem rankRaisingArgument_mk {r : ℕ} (q : Q r) (y : P r) :
    rankRaisingArgument q y = Quotient.mk _ ((lowerBlockPair q.out (0 : X r) (1 : B)) *
      rankRaisingSmoothingMatrix y) := by
  unfold rankRaisingArgument
  change rightTranslate (N (r + 1)) (rankRaisingSmoothingMatrix y)
    (lowerBlockQuotientChart (q, (0 : X r), (1 : B))) = _
  conv_lhs => rw [← Quotient.out_eq q]
  rw [lowerBlockQuotientChart_mk, rightTranslate_mk]

private theorem splitBottomRow_rankRaising_argument {r : ℕ} (q : Q r) (y : P r) :
    splitBottomRow ((lowerBlockPair q.out (0 : X r) (1 : B)) * rankRaisingSmoothingMatrix y) =
      (y.1, y.2.val.val.det) := by
  rw [rankRaisingSmoothingMatrix, lowerBlockPair_mul_lowerBlockPair]
  simp only [Matrix.zero_mul, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, zero_add, one_mul]
  exact splitBottomRow_lowerBlockPair _ y

section Coefficients

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type*} [NormedRing C] [NormedAlgebra ℝ C] [CompleteSpace C]
variable (σ : G (r + 1) →* Cˣ) (R : Cˣ →* (E →L[ℂ] E))
local notation "D" => DerivativeSmoothVectors 𝓘(ℝ, C) R
local notation "act" => representation 𝓘(ℝ, C) R

/-- Invariance of the scalar form under the image of the upper unipotent subgroup. -/
def IsMappedRankRaisingInvariant (L : D →L[ℂ] ℂ) : Prop :=
  ∀ (u : N (r + 1)) (v : D), L (act (σ u.val) v) = L v

/-- The row-tested larger-quotient coefficient, before the spectral power. -/
def mappedRankRaisingRowCoefficient (L : D →L[ℂ] ℂ) (v : D) (φ : 𝓢(W r, ℂ)) (q : Q (r + 1)) : ℂ :=
  φ (splitBottomRow q.out) * L (act (σ q.out) v)

private theorem mappedRankRaisingRowCoefficient_left (L : D →L[ℂ] ℂ)
    (hL : IsMappedRankRaisingInvariant σ R L) (v : D) (φ : 𝓢(W r, ℂ))
    (u : N (r + 1)) (g : G (r + 1)) :
    φ (splitBottomRow (u.val * g)) * L (act (σ (u.val * g)) v) =
      φ (splitBottomRow g) * L (act (σ g) v) := by
  rw [splitBottomRow_leftUnipotent, map_mul σ, map_mul, Module.End.mul_apply, hL]

/-- The row coefficient can be evaluated using any quotient representative. -/
theorem mappedRankRaisingRowCoefficient_mk (L : D →L[ℂ] ℂ)
    (hL : IsMappedRankRaisingInvariant σ R L) (v : D) (φ : 𝓢(W r, ℂ)) (g : G (r + 1)) :
    mappedRankRaisingRowCoefficient σ R L v φ (Quotient.mk _ g) =
      φ (splitBottomRow g) * L (act (σ g) v) := by
  let f (g : G (r + 1)) := φ (splitBottomRow g) * L (act (σ g) v)
  let h := mappedRankRaisingRowCoefficient_left σ R L hL v φ
  exact (RealEqualConvergence.out_eq_descend f h (Quotient.mk _ g)).trans (descend_mk _ f h g)

private theorem continuous_mappedRankRaisingRowCoefficient [FiniteDimensional ℝ C]
    (hR : IsContinuousRepresentation R) (hσ : Continuous σ) (L : D →L[ℂ] ℂ)
    (hL : IsMappedRankRaisingInvariant σ R L) (v : D) (φ : 𝓢(W r, ℂ)) :
    Continuous (mappedRankRaisingRowCoefficient σ R L v φ) := by
  let f (g : G (r + 1)) := φ (splitBottomRow g) * L (act (σ g) v)
  have hf : Continuous f := (φ.continuous.comp continuous_splitBottomRow).mul
    (L.continuous.comp ((continuous_representation_units R hR).comp (hσ.prodMk continuous_const)))
  let h := mappedRankRaisingRowCoefficient_left σ R L hL v φ
  have he : mappedRankRaisingRowCoefficient σ R L v φ = descend (N (r + 1)) f h :=
    funext (RealEqualConvergence.out_eq_descend f h)
  rw [he]
  exact RealEqualConvergence.continuous_descend h hf

private theorem mappedRankRaisingRowCoefficient_argument (L : D →L[ℂ] ℂ)
    (hL : IsMappedRankRaisingInvariant σ R L) (v : D) (φ : 𝓢(W r, ℂ)) (q : Q r) (y : P r) :
    mappedRankRaisingRowCoefficient σ R L v φ (rankRaisingArgument q y) =
      mappedRankRaisingAverageIntegrand σ R φ (L.comp (SmoothAction.derivativeAction 𝓘(ℝ, C) R
        (σ (lowerBlockPair q.out (0 : X r) (1 : B))))) v y := by
  rw [rankRaisingArgument_mk, mappedRankRaisingRowCoefficient_mk σ R L hL]
  unfold mappedRankRaisingAverageIntegrand
  rw [splitBottomRow_rankRaising_argument, map_mul σ, map_mul, Module.End.mul_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- The coefficient on the smaller quotient after the leading embedding. -/
def mappedRankRaisingLowerCoefficient (L : D →L[ℂ] ℂ) (v : D) (q : Q r) : ℂ :=
  L (act (σ (lowerBlockPair q.out (0 : X r) (1 : B))) v)

end Coefficients

private theorem continuous_trailingHeight : Continuous trailingHeight :=
  continuous_nnnorm.comp
    ((Units.continuous_val.comp (continuous_subtype_val : Continuous (fun h : B => h.val))).matrix_det)

private theorem coordinateMeasure_withDensity {r : ℕ} (ν : AdditiveHaarMeasure ℝ) (ρ : Measure B)
    [SigmaFinite ρ] : rankRaisingCoordinateMeasure r ν ρ =
      ((rectangularMeasure ν 1 (r + 1)).prod ρ).withDensity (fun y => (trailingHeight y.2 : ℝ≥0∞)) := by
  let := sigmaFinite_rect ν 1 (r + 1)
  exact prod_withDensity_right continuous_trailingHeight.measurable.coe_nnreal_ennreal

/-- A smooth coefficient restricted by an exponential-compatible homomorphism has a
one-step rank-raising identity with compact bottom-row tests, up to the positive measure
comparison scalar. The identity holds wherever the larger integrands are absolutely integrable. -/
def RealMappedSmoothRankRaisingRowStatement : Prop :=
  ∀ (r : ℕ) (D₀ : RealQuotientMeasureData r) (D₁ : RealQuotientMeasureData (r + 1))
    (_ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant],
    ρ ≠ 0 → ∃ c : ℝ, 0 < c ∧
      ∀ (C : Type*) [NormedRing C] [NormedAlgebra ℝ C] [CompleteSpace C] [FiniteDimensional ℝ C]
        (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        (σ : G (r + 1) →* Cˣ) (j : M r →ₗ[ℝ] C) (R : Cˣ →* (E →L[ℂ] E)),
      let V := DerivativeSmoothVectors 𝓘(ℝ, C) R
      IsContinuousRepresentation R → Continuous σ →
      (∀ Y : M r, σ (Langlands.LinearLieGroup.expUnit (M r) Y) =
        Langlands.LinearLieGroup.expUnit C (j Y)) → ∀ L : V →L[ℂ] ℂ,
      IsMappedRankRaisingInvariant σ R L → ∀ v : V,
        ∃ (k : ℕ) (w : Fin k → V) (φ : Fin k → 𝓢(W r, ℂ)),
          (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ {p : W r | p.2 ≠ 0}) ∧
          ∀ s : ℂ, (∀ i, Integrable (fun q => mappedRankRaisingRowCoefficient σ R L (w i) (φ i) q *
            realQuotientDetPower q s) D₁.measure) →
            Integrable (fun q => mappedRankRaisingLowerCoefficient σ R L v q * realQuotientDetPower q (s - 1)) D₀.measure ∧
            (c : ℂ) * (∫ q, mappedRankRaisingLowerCoefficient σ R L v q * realQuotientDetPower q (s - 1) ∂D₀.measure) =
              ∑ i, ∫ q, mappedRankRaisingRowCoefficient σ R L (w i) (φ i) q * realQuotientDetPower q s ∂D₁.measure

set_option maxHeartbeats 780000 in
theorem realMappedSmoothRankRaisingRow : RealMappedSmoothRankRaisingRowStatement := by
  intro r D₀ D₁ ν ρ _ _ _ hρ
  obtain ⟨c, hc, hInt⟩ := realRankRaisingIntegral r D₀ D₁ ν ρ hρ
  refine ⟨c, hc, ?_⟩
  intro C _ _ _ _ E _ _ _ σ j R V hR hσ hExp L hL v
  obtain ⟨k, w, φ, hφ, hVec⟩ := realRankRaisingMappedSmoothFactorization r ν ρ C E σ j R hR hσ hExp v
  refine ⟨k, w, φ, hφ, fun s hi => ?_⟩
  let η := (rectangularMeasure ν 1 (r + 1)).prod ρ
  let F (i : Fin k) := mappedRankRaisingRowCoefficient σ R L (w i) (φ i)
  let A (i : Fin k) := averagedRankRaisingKernel η (F i) s
  have hA (i : Fin k) := hInt (F i) (continuous_mappedRankRaisingRowCoefficient σ R hR hσ L hL (w i) (φ i)).measurable s (hi i)
  have hK : (fun q => mappedRankRaisingLowerCoefficient σ R L v q * realQuotientDetPower q (s - 1)) =
      fun q => ∑ i, A i q := by
    funext q
    let Lq := L.comp (SmoothAction.derivativeAction 𝓘(ℝ, C) R (σ (lowerBlockPair q.out (0 : X r) (1 : B))))
    change Lq v * realQuotientDetPower q (s - 1) = _
    rw [(hVec Lq).2, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    change (∫ y, mappedRankRaisingAverageIntegrand σ R (φ i) Lq (w i) y ∂rankRaisingCoordinateMeasure r ν ρ) *
        realQuotientDetPower q (s - 1) =
      realQuotientDetPower q (s - 1) * ∫ y, ((|y.2.val.val.det| : ℝ) : ℂ) * F i (rankRaisingArgument q y) ∂η
    rw [mul_comm, coordinateMeasure_withDensity]
    have hWeight : Measurable (fun y : P r => trailingHeight y.2) :=
      continuous_trailingHeight.measurable.comp measurable_snd
    rw [integral_withDensity_eq_integral_smul hWeight]
    congr 1
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun y => ?_
    change trailingHeight y.2 • mappedRankRaisingAverageIntegrand σ R (φ i) Lq (w i) y =
      ((|y.2.val.val.det| : ℝ) : ℂ) * mappedRankRaisingRowCoefficient σ R L (w i) (φ i) (rankRaisingArgument q y)
    rw [mappedRankRaisingRowCoefficient_argument σ R L hL]
    simp only [NNReal.smul_def, Complex.real_smul, trailingHeight, coe_nnnorm, Real.norm_eq_abs]
    rfl
  rw [hK]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => (hA i).1), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => (hA i).1), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => (hA i).2.symm

section Coefficients

variable {r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (R : G (r + 1) →* (E →L[ℂ] E))
local notation "D" => DerivativeSmoothVectors (I r) R

/-- Upper-unipotent invariance for a form on the larger group's genuine smooth vectors. -/
def IsRankRaisingInvariant (L : D →L[ℂ] ℂ) : Prop := IsMappedRankRaisingInvariant (MonoidHom.id _) R L

/-- The row-tested larger-quotient coefficient, before the spectral power. -/
def rankRaisingRowCoefficient (L : D →L[ℂ] ℂ) (v : D) (φ : 𝓢(W r, ℂ)) (q : Q (r + 1)) : ℂ :=
  mappedRankRaisingRowCoefficient (MonoidHom.id _) R L v φ q

/-- The coefficient on the smaller quotient after the leading embedding. -/
def rankRaisingLowerCoefficient (L : D →L[ℂ] ℂ) (v : D) (q : Q r) : ℂ :=
  mappedRankRaisingLowerCoefficient (MonoidHom.id _) R L v q

end Coefficients

/-- The smaller-quotient integral of a smooth coefficient is a finite sum of
larger-quotient integrals with compact bottom-row tests, up to the positive
measure comparison scalar. The integrals are compared at spectral points
where all the larger integrands are absolutely integrable. -/
def RealSmoothRankRaisingRowStatement : Prop :=
  ∀ (r : ℕ) (D₀ : RealQuotientMeasureData r) (D₁ : RealQuotientMeasureData (r + 1))
    (_ν : AdditiveHaarMeasure ℝ) (ρ : Measure B) [SigmaFinite ρ] [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant],
    ρ ≠ 0 → ∃ c : ℝ, 0 < c ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        (R : G (r + 1) →* (E →L[ℂ] E)),
      let V := DerivativeSmoothVectors (I r) R
      IsContinuousRepresentation R → ∀ L : V →L[ℂ] ℂ,
      IsRankRaisingInvariant R L → ∀ v : V,
        ∃ (k : ℕ) (w : Fin k → V) (φ : Fin k → 𝓢(W r, ℂ)),
          (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ {p : W r | p.2 ≠ 0}) ∧
          ∀ s : ℂ, (∀ i, Integrable (fun q => rankRaisingRowCoefficient R L (w i) (φ i) q *
            realQuotientDetPower q s) D₁.measure) →
            Integrable (fun q => rankRaisingLowerCoefficient R L v q * realQuotientDetPower q (s - 1)) D₀.measure ∧
            (c : ℂ) * (∫ q, rankRaisingLowerCoefficient R L v q * realQuotientDetPower q (s - 1) ∂D₀.measure) =
              ∑ i, ∫ q, rankRaisingRowCoefficient R L (w i) (φ i) q * realQuotientDetPower q s ∂D₁.measure

theorem realSmoothRankRaisingRow : RealSmoothRankRaisingRowStatement := by
  intro r D₀ D₁ ν ρ _ _ _ hρ
  obtain ⟨c, hc, h⟩ := realMappedSmoothRankRaisingRow r D₀ D₁ ν ρ hρ
  refine ⟨c, hc, ?_⟩
  intro E _ _ _ R V hR L hL v
  exact h (M r) E (MonoidHom.id _) LinearMap.id R hR continuous_id (fun _ => rfl) L hL v

end Langlands.Global.RankinSelbergGlobal.RealRankRaisingIntegral
