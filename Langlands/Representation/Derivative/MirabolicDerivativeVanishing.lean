import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement

/-!
# Mirabolic representations with vanishing derivatives

A smooth representation of `P_(M+1)` all of whose derivatives `Ψ⁻ ∘ (Φ⁻)^j` vanish is zero
(Bernstein–Zelevinsky 1977, §3.5). The proof is a descending induction on the rank: the
`P_1` boundary holds because the radical of `P_1` is trivial, and each positive rank uses
`subsingleton_of_psiMinus_phiMinus`. As a consequence every nonzero smooth representation
of `P_(N+1)` has positive derivative level, which is
`Langlands.Derivative.MirabolicDerivativeDetection`. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Jacquet.Localization

universe uF uV

section Detection

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The radical of `P_1` is trivial, so it acts trivially on every representation. -/
theorem radical_acts_trivially_zero :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier))
      (u : radical 0 F.Carrier) (v : X),
      X.representation (u : mirabolic 0 F.Carrier) v = v := by
  intro X u v
  rw [Subsingleton.elim u 1]
  simp

/-- If the radical acts trivially, the trivial-character relations vanish. -/
theorem relations_one_eq_bot {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (mirabolic n F.Carrier) V)
    (h : ∀ (u : radical n F.Carrier) (v : V), ρ (u : mirabolic n F.Carrier) v = v) :
    relations ρ (radical n F.Carrier) 1 = ⊥ := by
  refine eq_bot_iff.mpr (Submodule.span_le.mpr ?_)
  rintro _ ⟨⟨u, v⟩, rfl⟩
  simp [h]

/-- The `P_1` boundary: a smooth representation of `P_1` with vanishing `Ψ⁻` is zero. -/
theorem subsingleton_of_psiMinus_zero :
    letI := T.topology
    ∀ Z : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier),
      Subsingleton ((Mirabolic.psiMinus T 0).obj Z) → Subsingleton Z := by
  let := T.topology
  intro Z h
  change Subsingleton (Coinvariants Z.representation (radical 0 F.Carrier) 1) at h
  have hbot := relations_one_eq_bot Z.representation (radical_acts_trivially_zero T Z)
  refine ⟨fun x y => ?_⟩
  have hxy : mk Z.representation (radical 0 F.Carrier) 1 x =
      mk Z.representation (radical 0 F.Carrier) 1 y := Subsingleton.elim _ _
  rw [mk_eq_iff, hbot, Submodule.mem_bot, sub_eq_zero] at hxy
  exact hxy

/-- Derivatives of the same rank and `Φ⁻`-count agree after any rank transports. -/
theorem subsingleton_rankCast_mirabolicDerivative_congr {N n n' j j' : ℕ} (h : N = n + j)
    (h' : N = n' + j') (hn : n = n') (hj : j = j') :
    letI := T.topology
    ∀ Z : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj Z) →
      Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' j').obj Z) := by
  subst hn
  subst hj
  exact fun _ hZ => hZ

/-- BZ77 §3.5: a smooth representation of `P_(M+1)` all of whose derivatives
`Ψ⁻ ∘ (Φ⁻)^j`, transported to the ranks `M = n + j`, vanish is zero. -/
theorem subsingleton_of_forall_mirabolicDerivative (M : ℕ) :
    letI := T.topology
    ∀ Z : SmoothRep.{0, uF, uV} ℂ (mirabolic M F.Carrier),
      (∀ (n j : ℕ) (h : M = n + j),
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj Z)) →
      Subsingleton Z := by
  let := T.topology
  induction M with
  | zero =>
    intro Z hZ
    exact subsingleton_of_psiMinus_zero T Z (hZ 0 0 rfl)
  | succ m ih =>
    intro Z hZ
    refine subsingleton_of_psiMinus_phiMinus T ψ m Z (hZ (m + 1) 0 rfl) ?_
    refine ih ((Mirabolic.phiMinus T ψ m).obj Z) fun n j h => ?_
    subst h
    exact hZ n (j + 1) rfl

/-- Every order-`k` derivative of `A`, `1 ≤ k ≤ N + 1`, vanishes only if `A` vanishes. -/
theorem subsingleton_of_forall_mirabolicDerivativeOfOrder {N : ℕ} :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      (∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
        Subsingleton ((mirabolicDerivativeOfOrder T ψ N k hk).obj A)) →
      Subsingleton A := by
  let := T.topology
  intro A hA
  refine subsingleton_of_forall_mirabolicDerivative T ψ N A fun n j h => ?_
  have hk : 0 < j + 1 ∧ j + 1 ≤ N + 1 := by omega
  exact subsingleton_rankCast_mirabolicDerivative_congr T ψ (mirabolic_rank_eq_of_order hk) h
    (by omega) (by omega) A (hA (j + 1) hk)

end Detection

/-- `Langlands.Derivative.MirabolicDerivativeDetection`: every nonzero smooth representation
of `P_(N+1)` has positive derivative level. The exact name
`Langlands.Derivative.mirabolicDerivativeDetection` is left free for the module
`MirabolicDerivativeDetectionProof`. -/
theorem derivativeDetection {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicDerivativeDetection.{uF, uV} F T := by
  let := T.topology
  intro ψ N A hA
  rcases Nat.eq_zero_or_pos (level T ψ A) with h0 | h0
  · exfalso
    rw [level_eq_zero_iff] at h0
    have hsub : Subsingleton A :=
      subsingleton_of_forall_mirabolicDerivativeOfOrder T ψ A fun k hk =>
        not_nontrivial_iff_subsingleton.mp (h0 k hk)
    exact false_of_nontrivial_of_subsingleton A
  · exact h0

end Langlands.Derivative.Mirabolic
