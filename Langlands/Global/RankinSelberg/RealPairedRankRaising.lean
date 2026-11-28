import Langlands.Global.RankinSelberg.RealSmoothRankRaisingRow
import Langlands.Global.RankinSelberg.RealPairedSmoothRowAbsorption
import Langlands.Global.RankinSelberg.DualExpansionData

/-! # One-step rank raising for the genuine real Whittaker pair -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 780000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors Langlands.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal CompletedProjectiveRepresentation
open RealRankRaisingIntegral RealPaddedExponential
open RealPaddedWhittakerProduct (oppositeScale)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel
private local instance : MeasurableSpace (lowerTriangularSubgroup 1 ℝ) := borel _
private local instance : BorelSpace (lowerTriangularSubgroup 1 ℝ) := ⟨rfl⟩

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "Q" => fun n : ℕ => LeftUnipotentQuotient n ℝ
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "Tail" => lowerTriangularSubgroup 1 ℝ
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "Vec" => fun n : ℕ => Fin (n + 1) → ℝ
local notation "X" => fun n : ℕ => Matrix (Fin 1) (Fin (n + 1)) ℝ

private def splitRow (r : ℕ) : Vec (r + 1) ≃L[ℝ] (X r × ℝ) :=
  ({ toFun := fun x => (fun _ i => x i.castSucc, x (Fin.last (r + 1)))
     invFun := fun p => Fin.snoc (p.1 0) p.2
     left_inv := fun x => Fin.snoc_init_self x
     right_inv := by
       intro p
       apply Prod.ext
       · ext i j
         have hi : i = 0 := Subsingleton.elim _ _
         subst i
         change Fin.snoc (α := fun _ => ℝ) (p.1 0) p.2 j.castSucc = p.1 0 j
         simp
       · change Fin.snoc (α := fun _ => ℝ) (p.1 0) p.2 (Fin.last (r + 1)) = p.2
         simp
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Vec (r + 1) ≃ₗ[ℝ] (X r × ℝ)).toContinuousLinearEquiv

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, B)
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "act" => DerivativeSmoothVectors.representation I (productAction A R)

/-- The paired scalar evaluation on the common quotient using both leading-block embeddings. -/
def paddedPairCoefficient (m : ℕ) (h : ∀ i, m ≤ n i) (L : D →L[ℂ] ℂ) (v : D) (q : Q m) : ℂ :=
  L (act (padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (h i)) q.out) v)

/-- A smooth real Whittaker pair raises the common quotient rank by one. The compact bottom-row
weights can be absorbed if one of the ambient ranks is still strictly larger. -/
def RealPairedRankRaisingStepStatement : Prop :=
  ∀ (r : ℕ) (D₀ : RealQuotientMeasureData r) (D₁ : RealQuotientMeasureData (r + 1))
    (_ν : AdditiveHaarMeasure ℝ) (ρ : Measure Tail) [SigmaFinite ρ] [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant],
    ρ ≠ 0 → ∃ c : ℝ, 0 < c ∧
      ∀ (_hR : ∀ i, IsContinuousRepresentation (R i)) (a : ℝˣ) (L : D →L[ℂ] ℂ) (h : ∀ i, r + 1 ≤ n i),
        (∀ (g : Bˣ) (_hg : ∀ i, unitProjection A i g ∈ N (n i)) (w : D),
          L (act g w) = (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g)) * L w) →
        IsMappedRankRaisingInvariant (padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (h i)))
          (productAction A R) L →
        ∀ v : D, ∃ (k : ℕ) (w : Fin k → D) (φ : Fin k → 𝓢(Vec (r + 1), ℂ)),
          (∀ i, HasCompactSupport (φ i)) ∧
          (∀ s : ℂ, (∀ i, Integrable (fun q => paddedPairCoefficient n E R (r + 1) h L (w i) q *
            φ i (row q.out) * realQuotientDetPower q s) D₁.measure) →
            Integrable (fun q => paddedPairCoefficient n E R r (fun i => (Nat.le_succ r).trans (h i)) L v q *
              realQuotientDetPower q (s - 1)) D₀.measure ∧
            (c : ℂ) * (∫ q, paddedPairCoefficient n E R r (fun i => (Nat.le_succ r).trans (h i)) L v q *
              realQuotientDetPower q (s - 1) ∂D₀.measure) =
              ∑ i, ∫ q, paddedPairCoefficient n E R (r + 1) h L (w i) q * φ i (row q.out) *
                realQuotientDetPower q s ∂D₁.measure) ∧
          ∀ i : Fin 2, r + 1 < n i → ∃ w' : Fin k → D, ∀ j q,
            paddedPairCoefficient n E R (r + 1) h L (w' j) q =
              paddedPairCoefficient n E R (r + 1) h L (w j) q * φ j (row q.out)

theorem realPairedRankRaisingStep : RealPairedRankRaisingStepStatement n E R := by
  intro r D₀ D₁ ν ρ _ _ _ hρ
  obtain ⟨c, hc, hRaise⟩ := realMappedSmoothRankRaisingRow r D₀ D₁ ν ρ hρ
  refine ⟨c, hc, ?_⟩
  intro hR a L h hCov hInv v
  let σ := padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (h i))
  let j := padProductLie (fun i => n i + 1) (fun i => Nat.succ_le_succ (h i))
  let P := productAction A R
  obtain ⟨hσ, he⟩ := realPaddedProductExponential (fun i => n i + 1) (fun i => Nat.succ_le_succ (h i))
  obtain ⟨k, w, ψ, hψ, hInt⟩ := hRaise B (Carrier E) σ j P (isContinuous_productAction A R hR) hσ he L hInv v
  let φ (i : Fin k) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (splitRow r) (ψ i)
  have hSmall (q : Q r) : mappedRankRaisingLowerCoefficient σ P L v q =
      paddedPairCoefficient n E R r (fun i => (Nat.le_succ r).trans (h i)) L v q := by
    unfold mappedRankRaisingLowerCoefficient paddedPairCoefficient
    rw [RealUnequalLastRowDescent.lowerBlockPair_zero_one]
    apply congrArg (fun p : Bˣ => L (act p v))
    apply Units.ext
    funext i
    change (padGL (Nat.succ_le_succ (h i)) (padGL (Nat.le_succ (r + 1)) q.out)).val = _
    exact congrArg Units.val (Unfolding.padGL_comp (Nat.le_succ (r + 1)) (Nat.succ_le_succ (h i)) q.out)
  have hLarge (i : Fin k) (q : Q (r + 1)) : mappedRankRaisingRowCoefficient σ P L (w i) (ψ i) q =
      paddedPairCoefficient n E R (r + 1) h L (w i) q * φ i (row q.out) := by
    change ψ i (splitBottomRow q.out) * L (act (σ q.out) (w i)) =
      L (act (σ q.out) (w i)) * ψ i (splitBottomRow q.out)
    exact mul_comm _ _
  refine ⟨k, w, φ, fun i => ?_, fun s hs => ?_, fun i hi => ?_⟩
  · exact (hψ i).1.comp_homeomorph (splitRow r).toHomeomorph
  · have hI (i : Fin k) : Integrable (fun q => mappedRankRaisingRowCoefficient σ P L (w i) (ψ i) q *
        realQuotientDetPower q s) D₁.measure := by
      simpa only [hLarge i] using hs i
    simpa only [hSmall, hLarge] using hInt s hI
  · choose w' hw' using fun l => RealPairedSmoothRowAbsorption.realPairedSmoothRowAbsorption n E R
      hR a L hCov (r + 1) h i hi (w l) (φ l)
    exact ⟨w', fun l q => hw' l q.out⟩

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, Langlands.GeneralLinear ((n i) + 1) ℝ →* (E i →L[ℂ] E i))

/-- The assertion for representations on complex Banach spaces. -/
def RealPairedRankRaisingStepBanachStatement [∀ i, CompleteSpace (E i)] : Prop :=
  RealPairedRankRaisingStepStatement n E R

theorem realPairedRankRaisingStepBanach [∀ i, CompleteSpace (E i)] : RealPairedRankRaisingStepBanachStatement n E R :=
  realPairedRankRaisingStep n E R

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
