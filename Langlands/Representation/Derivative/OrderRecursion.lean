import Langlands.Representation.Derivative.Homogeneity

/-!
# Source-rank recursion for actual mirabolic derivatives

Equality transports commute with the published normalized minus functors.
The source-rank/order derivative applies its largest-rank `Φ⁻` first.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

theorem mirabolicRankCast_trans (T : F.TopologicalData) {a b c : ℕ}
    (h : a = b) (h' : b = c) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicRankCast T h' =
      mirabolicRankCast T (h.trans h') := by
  subst h h'
  exact Functor.id_comp _

theorem mirabolicRankCast_symm_comp (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicRankCast T h.symm =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (mirabolic a F.Carrier)) := by
  subst h
  exact Functor.id_comp _

theorem mirabolicRankCast_comp_symm (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h.symm ⋙ mirabolicRankCast T h =
      𝟭 (SmoothRep.{0, uF, uV} ℂ (mirabolic b F.Carrier)) := by
  subst h
  exact Functor.id_comp _

theorem psiMinus_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ Mirabolic.psiMinus T b =
      Mirabolic.psiMinus T a ⋙ generalLinearRankCast T h := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

theorem phiMinus_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T (congrArg (· + 1) h) ⋙ Mirabolic.phiMinus T ψ b =
      Mirabolic.phiMinus T ψ a ⋙ mirabolicRankCast T h := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

theorem phiMinusIterate_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a b : ℕ} (h : a = b) (j : ℕ) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T (congrArg (· + j) h) ⋙ phiMinusIterate T ψ b j =
      phiMinusIterate T ψ a j ⋙ mirabolicRankCast T h := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

theorem mirabolicDerivative_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a b : ℕ} (h : a = b) (j : ℕ) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T (congrArg (· + j) h) ⋙ mirabolicDerivative T ψ b j =
      mirabolicDerivative T ψ a j ⋙ generalLinearRankCast T h := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

theorem mirabolicDerivativeOfOrder_rankCast (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a b : ℕ} (h : a = b) (i : ℕ)
    (ha : 0 < i ∧ i ≤ a + 1) (hb : 0 < i ∧ i ≤ b + 1) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ⋙ mirabolicDerivativeOfOrder T ψ b i hb =
      mirabolicDerivativeOfOrder T ψ a i ha ⋙
        generalLinearRankCast T (congrArg (fun n => n + 1 - i) h) := by
  subst h
  exact (Functor.id_comp _).trans (Functor.comp_id _).symm

/-- One largest-rank step, with independently supplied source and target transports. -/
theorem mirabolicDerivative_succ_transport (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N m n j : ℕ) (e : m = n) (h : N = n + j) (h' : N + 1 = m + (j + 1)) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h' ⋙ mirabolicDerivative T ψ m (j + 1) ⋙
        generalLinearRankCast T e =
      Mirabolic.phiMinus T ψ N ⋙ mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j := by
  subst e
  subst h
  simp only [mirabolicRankCast_refl, generalLinearRankCast_refl, Functor.id_comp,
    Functor.comp_id, mirabolicDerivative_succ]

/-- At order `i+1`, apply `Φ⁻` first and then the order-`i` derivative.
The displayed target cast accounts for natural-number subtraction. -/
theorem mirabolicDerivativeOfOrder_succ (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N i : ℕ) (hi : 0 < i ∧ i ≤ N + 1)
    (hi' : 0 < i + 1 ∧ i + 1 ≤ N + 1 + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ (N + 1) (i + 1) hi' ⋙
        generalLinearRankCast T (show N + 1 + 1 - (i + 1) = N + 1 - i by omega) =
      Mirabolic.phiMinus T ψ N ⋙ mirabolicDerivativeOfOrder T ψ N i hi := by
  let _ := T.topology
  cases i with
  | zero => omega
  | succ j =>
    rw [mirabolicDerivativeOfOrder_eq, mirabolicDerivativeOfOrder_eq, Functor.assoc]
    exact mirabolicDerivative_succ_transport.{uF, uV} T ψ N
      (N + 1 + 1 - (j + 1 + 1)) (N + 1 - (j + 1)) j
      (by omega) (mirabolic_rank_eq_of_order hi) (mirabolic_rank_eq_of_order hi')

/-- Natural isomorphism form of the source-rank recursion, on every morphism. -/
def mirabolicDerivativeOfOrderSuccIso (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N i : ℕ) (hi : 0 < i ∧ i ≤ N + 1)
    (hi' : 0 < i + 1 ∧ i + 1 ≤ N + 1 + 1) :
    letI := T.topology
    mirabolicDerivativeOfOrder.{uF, uV} T ψ (N + 1) (i + 1) hi' ⋙
        generalLinearRankCast T (show N + 1 + 1 - (i + 1) = N + 1 - i by omega) ≅
      Mirabolic.phiMinus T ψ N ⋙ mirabolicDerivativeOfOrder T ψ N i hi :=
  letI := T.topology
  eqToIso (mirabolicDerivativeOfOrder_succ T ψ N i hi hi')

end Langlands.Derivative
