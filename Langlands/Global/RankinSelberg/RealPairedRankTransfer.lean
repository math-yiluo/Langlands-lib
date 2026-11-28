import Langlands.Global.RankinSelberg.RealPairedRankRaising

/-! # Iterated rank raising for real paired quotient integrals -/

noncomputable section

open MeasureTheory
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 900000

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
local notation "last" => Langlands.RankinSelberg.lastRow
local notation "Vec" => fun n : ℕ => Fin (n + 1) → ℝ

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)]
  (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "A" => fun i => Mat (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, B)
local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "act" => DerivativeSmoothVectors.representation I (productAction A R)
local notation "Rows" => fun m => 𝓢(Vec m, ℂ)
local notation "Terms" => fun m => D × Option (Rows m)

/-- The scalar paired quotient kernel, with an optional Schwartz test of the last row. -/
def paddedPairKernel (m : ℕ) (hm : ∀ i, m ≤ n i) (L : D →L[ℂ] ℂ)
    (t : Terms m) (s : ℂ) (q : Q m) : ℂ :=
  paddedPairCoefficient n E R m hm L t.1 q * (t.2.elim 1 fun φ => φ (last q.out)) *
    realQuotientDetPower q s

omit [∀ i, CompleteSpace (E i)] in
theorem paddedPairKernel_none (m : ℕ) (hm : ∀ i, m ≤ n i) (L : D →L[ℂ] ℂ)
    (v : D) (s : ℂ) : paddedPairKernel n E R m hm L (v, none) s =
      fun q => paddedPairCoefficient n E R m hm L v q * realQuotientDetPower q s := by
  funext q
  simp [paddedPairKernel]

omit [∀ i, CompleteSpace (E i)] in
theorem paddedPairKernel_some (m : ℕ) (hm : ∀ i, m ≤ n i) (L : D →L[ℂ] ℂ)
    (v : D) (φ : Rows m) (s : ℂ) : paddedPairKernel n E R m hm L (v, some φ) s =
      fun q => paddedPairCoefficient n E R m hm L v q * φ (last q.out) * realQuotientDetPower q s := rfl

/-- The terminal row is present exactly when the comparison group fills both ambient ranks. -/
def IsPairedTerminalRow (m : ℕ) : Option (Rows m) → Prop
  | none => ∃ i, m < n i
  | some φ => (∀ i, n i = m) ∧ HasCompactSupport φ

/-- The finite integral comparison from a smaller common rank to the terminal rank. -/
def HasPairedRankTransfer (top : ℕ) (hTop : ∀ i, top ≤ n i)
    (μ : (m : ℕ) → RealQuotientMeasureData m) (L : D →L[ℂ] ℂ) (r : ℕ) (hr : r < top) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ v : D,
    ∃ (k : ℕ) (t : Fin k → Terms top), (∀ i, IsPairedTerminalRow n top (t i).2) ∧
      ∀ s : ℂ, (∀ i, Integrable (paddedPairKernel n E R top hTop L (t i) s) (μ top).measure) →
        Integrable (paddedPairKernel n E R r (fun i => hr.le.trans (hTop i)) L (v, none) (s - (top - r : ℕ)))
          (μ r).measure ∧
        (c : ℂ) * (∫ q, paddedPairKernel n E R r (fun i => hr.le.trans (hTop i)) L (v, none)
          (s - (top - r : ℕ)) q ∂(μ r).measure) =
          ∑ i, ∫ q, paddedPairKernel n E R top hTop L (t i) s q ∂(μ top).measure

/-- Iterating rank raising gives the ordinary terminal rank, with a Schwartz row in the equal-rank case. -/
def RealPairedRankTransferStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (top : ℕ) (hTop : ∀ i, top ≤ n i) (μ : (m : ℕ) → RealQuotientMeasureData m)
    (_ν : AdditiveHaarMeasure ℝ) (ρ : Measure Tail) [SigmaFinite ρ] [ρ.IsHaarMeasure] [ρ.IsMulRightInvariant],
    ρ ≠ 0 → ∀ (a : ℝˣ) (L : D →L[ℂ] ℂ),
      (∀ (g : Bˣ) (_hg : ∀ i, unitProjection A i g ∈ N (n i)) (w : D),
        L (act g w) = (∏ i, realWhittakerCharacter (oppositeScale a i) (unitProjection A i g)) * L w) →
      (∀ (m : ℕ) (hm : ∀ i, m ≤ n i) (u : N m) (w : D), L (act
        (padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i)) u.val) w) = L w) →
      ∀ (r : ℕ) (hr : r < top), HasPairedRankTransfer n E R top hTop μ L r hr

private theorem rank_shift {r m : ℕ} (h : r < m) (s : ℂ) :
    s - (m - (r + 1) : ℕ) - 1 = s - (m - r : ℕ) := by
  rw [show m - r = m - (r + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  ring

set_option maxHeartbeats 1300000 in
theorem realPairedRankTransfer : RealPairedRankTransferStatement n E R := by
  intro hR top hTop μ ν ρ _ _ _ hρ a L hCov hInv r hr
  let Goal (j : ℕ) := ∀ hj : j < top, HasPairedRankTransfer n E R top hTop μ L j hj
  have hGoal : Goal r := by
    refine Nat.decreasingInduction (motive := fun j _ => Goal j) ?_ ?_ hr.le
    · intro k hk ih hk'
      let hNext (i : Fin 2) : k + 1 ≤ n i := (show k + 1 ≤ top from hk).trans (hTop i)
      obtain ⟨c₀, hc₀, hstep⟩ := realPairedRankRaisingStep n E R k (μ k) (μ (k + 1)) ν ρ hρ
      have hstep := hstep hR a L hNext hCov (hInv (k + 1) hNext)
      by_cases htop : k + 1 = top
      · subst top
        refine ⟨c₀, hc₀, fun v => ?_⟩
        obtain ⟨l, w, ψ, hψ, hI, hAbs⟩ := hstep v
        by_cases hStrict : ∃ i, k + 1 < n i
        · obtain ⟨i, hi⟩ := hStrict
          obtain ⟨w', hw'⟩ := hAbs i hi
          refine ⟨l, fun j => (w' j, none), fun _ => ⟨i, hi⟩, fun s hs => ?_⟩
          have hw (j : Fin l) (q : Q (k + 1)) : paddedPairCoefficient n E R (k + 1) hNext L (w j) q *
              ψ j (last q.out) = paddedPairCoefficient n E R (k + 1) hNext L (w' j) q := (hw' j q).symm
          have hLarge (j : Fin l) : Integrable (fun q => paddedPairCoefficient n E R (k + 1) hNext L (w j) q *
              ψ j (last q.out) * realQuotientDetPower q s) (μ (k + 1)).measure := by
            simpa only [hw j, paddedPairKernel_none] using hs j
          simpa only [hw, paddedPairKernel_none, Nat.add_sub_cancel_left, Nat.cast_one]
            using hI s hLarge
        · have he (i : Fin 2) : n i = k + 1 := le_antisymm (by
            by_contra! hn
            exact hStrict ⟨i, hn⟩) (hTop i)
          refine ⟨l, fun j => (w j, some (ψ j)), fun j => ⟨he, hψ j⟩, fun s hs => ?_⟩
          simpa only [paddedPairKernel_none, paddedPairKernel_some, Nat.add_sub_cancel_left, Nat.cast_one]
            using hI s hs
      · have hlt : k + 1 < top := lt_of_le_of_ne hk htop
        obtain ⟨c₁, hc₁, hup⟩ := ih hlt
        refine ⟨c₀ * c₁, mul_pos hc₀ hc₁, fun v => ?_⟩
        obtain ⟨l, w, ψ, _, hI, hAbs⟩ := hstep v
        obtain ⟨w', hw'⟩ := hAbs 0 (hlt.trans_le (hTop 0))
        choose K t ht hUp using fun j => hup (w' j)
        let J := Σ j : Fin l, Fin (K j)
        let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
        refine ⟨Fintype.card J, fun i => t (e i).1 (e i).2, fun i => ht (e i).1 (e i).2, fun s hs => ?_⟩
        let z := s - (top - (k + 1) : ℕ)
        let f (j : Fin l) (q : Q (k + 1)) := paddedPairCoefficient n E R (k + 1) hNext L (w j) q *
          ψ j (last q.out) * realQuotientDetPower q z
        have hF (j : Fin l) (q : Q (k + 1)) : f j q = paddedPairKernel n E R (k + 1) hNext L
            (w' j, none) z q := by
          unfold f paddedPairKernel
          rw [hw' j q]
          simp
        have hTerm (j : Fin l) (i : Fin (K j)) : Integrable (paddedPairKernel n E R top hTop L (t j i) s)
            (μ top).measure := by
          let p : J := ⟨j, i⟩
          have oneTerm := hs (e.symm p)
          change Integrable (paddedPairKernel n E R top hTop L
            (t (e (e.symm p)).1 (e (e.symm p)).2) s) (μ top).measure at oneTerm
          rw [e.apply_symm_apply] at oneTerm
          exact oneTerm
        have hu (j : Fin l) := hUp j s (hTerm j)
        have hFi (j : Fin l) : Integrable (f j) (μ (k + 1)).measure := by
          simpa only [funext (hF j)] using (hu j).1
        obtain ⟨hi, hEq⟩ := hI z hFi
        have hz : z - 1 = s - (top - k : ℕ) := rank_shift hk s
        rw [hz] at hi hEq
        refine ⟨by simpa only [paddedPairKernel_none] using hi, ?_⟩
        calc
          _ = (c₁ : ℂ) * ∑ j, ∫ q, f j q ∂(μ (k + 1)).measure := by
            rw [Complex.ofReal_mul, mul_comm (c₀ : ℂ) (c₁ : ℂ), mul_assoc]
            congr 1
            simpa only [paddedPairKernel_none] using hEq
          _ = ∑ j, (c₁ : ℂ) * ∫ q, f j q ∂(μ (k + 1)).measure := Finset.mul_sum _ _ _
          _ = ∑ j, ∑ i, ∫ q, paddedPairKernel n E R top hTop L (t j i) s q ∂(μ top).measure := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simpa only [funext (hF j)] using (hu j).2
          _ = _ := by
            let F (p : J) := ∫ q, paddedPairKernel n E R top hTop L (t p.1 p.2) s q ∂(μ top).measure
            exact (Fintype.sum_sigma F).symm.trans (e.sum_comp F).symm
    · intro h
      exact (lt_irrefl _ h).elim
  exact hGoal hr

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
