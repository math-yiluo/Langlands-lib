import Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
import Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
import Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement

/-!
# Proof of Bernstein–Zelevinsky (1977), Proposition 3.8

Induction on the number `j` of `Φ⁻` steps, peeling `Φ⁻` off at the largest rank first:
`mirabolicDerivative n (j + 1) = phiMinus (n + j) ⋙ mirabolicDerivative n j` holds
definitionally. Each `Φ⁻` step keeps a left-nondegenerate `|det|`-pairing; at `j = 0`
highestness and detection force `Φ⁻ A = 0`, the radical acts trivially, and the pairing
descends through `Ψ⁻`. The `Φ⁻` step is `phiMinus_nondegeneratePairing`. See the paired
Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

open scoped NNReal

universe uF uV uW

section Assembly

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A rank transport of `Φ⁻ X` is `Φ⁻` of the transported `X`, so a vanishing derivative
of `X` with one more `Φ⁻` step is a vanishing derivative of `Φ⁻ X`. -/
theorem subsingleton_rankCast_phiMinus {a n' i : ℕ} (h : a = n' + i)
    (h' : a + 1 = n' + (i + 1)) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (a + 1) F.Carrier),
      Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' (i + 1)).obj X) →
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj
        ((Mirabolic.phiMinus T ψ a).obj X)) := by
  subst h
  exact fun _ hX => hX

/-- The induction on the number `j` of `Φ⁻` steps, given the `Φ⁻` pairing step. -/
theorem highestDerivativePairing_core
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0)
    (j : ℕ) :
    letI := T.topology
    ∀ (n : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (n + j) F.Carrier)),
      (∀ (n' i : ℕ) (h : n + j = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (n + j + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((mirabolicDerivative T ψ n j).obj A).representation
            ((mirabolicDerivative T ψ n j).obj B).representation (fun _ => (1 : ℂ)),
          ∀ v : (mirabolicDerivative T ψ n j).obj A,
            (∀ w : (mirabolicDerivative T ψ n j).obj B, γ.val v w = 0) → v = 0 := by
  let := T.topology
  induction j with
  | zero =>
    intro n A B hhigh β hβ
    have hrad : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v := by
      cases n with
      | zero => exact radical_acts_trivially_zero T A
      | succ m =>
        refine radical_acts_trivially_of_phiMinus T ψ m A ?_
        refine subsingleton_of_forall_mirabolicDerivative T ψ m _ fun n' i h => ?_
        subst h
        exact hhigh n' (i + 1) rfl (by omega)
    obtain ⟨γ, hγ⟩ := psiMinus_nondegeneratePairing T n A B hrad β hβ
    exact ⟨γ, hγ⟩
  | succ j ih =>
    intro n A B hhigh β hβ
    obtain ⟨β', hβ'⟩ := hΦ (n + j) A B β hβ
    refine ih n ((Mirabolic.phiMinus T ψ (n + j)).obj A) ((Mirabolic.phiMinus T ψ (n + j)).obj B)
      (fun n' i h hlt => ?_) β' hβ'
    exact subsingleton_rankCast_phiMinus T ψ h (by omega) A (hhigh n' (i + 1) (by omega) hlt)

/-- The core induction, after an arbitrary rank transport `N = n + j`. -/
theorem highestDerivativePairing_cast
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0)
    {N n j : ℕ} (h : N = n + j) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier)),
      (∀ (n' i : ℕ) (h' : N = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms
            ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj A).representation
            ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj B).representation
            (fun _ => (1 : ℂ)),
          ∀ v : (mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj A,
            (∀ w : (mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj B,
              γ.val v w = 0) → v = 0 := by
  subst h
  exact highestDerivativePairing_core T ψ hΦ j n

end Assembly

/-- Proposition 3.8 from the `Φ⁻` pairing step for every character. -/
theorem mirabolicHighestDerivativePairing_of_phiMinusStep {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hΦ : letI := T.topology
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (m : ℕ)
        (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier))
        (β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (m + 1 + 1)) g.val : ℝ≥0) : ℝ) : ℂ))),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.phiMinus T ψ m).obj A).representation
            ((Mirabolic.phiMinus T ψ m).obj B).representation
            (fun h => ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ)),
          ∀ v : (Mirabolic.phiMinus T ψ m).obj A,
            (∀ w : (Mirabolic.phiMinus T ψ m).obj B, γ.val v w = 0) → v = 0) :
    MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T := by
  let := T.topology
  intro ψ N A B k hk _ hhigh β hβ
  refine highestDerivativePairing_cast T ψ (hΦ ψ) (mirabolic_rank_eq_of_order hk) A B ?_ β hβ
  intro n' i h' hlt
  have hj : 0 < i + 1 ∧ i + 1 ≤ N + 1 := by omega
  exact subsingleton_rankCast_mirabolicDerivative_congr T ψ (mirabolic_rank_eq_of_order hj) h'
    (by omega) (by omega) A (hhigh (i + 1) hj (by omega))

end Langlands.Derivative.Mirabolic

namespace Langlands.Derivative

universe uF uV uW

/-- Bernstein–Zelevinsky (1977), Proposition 3.8: the highest derivative of `A` keeps a
left-nondegenerate pairing. -/
theorem mirabolicHighestDerivativePairing {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicHighestDerivativePairingStatement.{uF, uV, uW} F T :=
  Mirabolic.mirabolicHighestDerivativePairing_of_phiMinusStep F T fun ψ m =>
    Mirabolic.phiMinus_nondegeneratePairing T ψ m

end Langlands.Derivative
