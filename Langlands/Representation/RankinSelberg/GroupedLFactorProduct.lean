import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction

/-! # L-polynomials of grouped square-integrable blocks -/

noncomputable section

namespace Langlands.RankinSelberg

open CategoryTheory MeasureTheory HarmonicAnalysis GeneralLinear Polynomial

universe uF uV uW uV' uW'

variable {p : ℕ} [Fact p.Prime]

section Grouped

variable (F : PadicField.{uF} p)

local instance groupedCanonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- Rank transport on bundled smooth representations leaves the factor relation
unchanged. Both rank equalities are explicit. -/
theorem isPadicRankLPolynomial_cast_iff {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier)) (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν.val (hm ▸ A).representation (hn ▸ B).representation P ↔
      IsPadicRankLPolynomial F ψ ν.val A.representation B.representation P := by
  subst hm hn
  rfl

/-- Common group exponents cancel the negative block twists inside the factor
relation, including the rank transports supplied by the grouping witnesses. -/
theorem isPadicRankLPolynomial_cast_normalized_twist_iff
    {m m' n n' : ℕ} (hm : m = m') (hn : n = n')
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear m' F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n' F.Carrier))
    {s s' z z' : ℝ} (hs : s = s') (hz : z = z') (P : ℂ[X]) :
    IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm m) s
        ((hm.symm ▸ F.canonicalTopologicalData.segmentFactor A (-s')).representation))
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) z
        ((hn.symm ▸ F.canonicalTopologicalData.segmentFactor B (-z')).representation)) P ↔
      IsPadicRankLPolynomial F ψ ν.val A.representation B.representation P := by
  subst hm hn hs hz
  change IsPadicRankLPolynomial F ψ ν.val
    (realPowerTwist _ s (realPowerTwist _ (-s) A.representation))
    (realPowerTwist _ z (realPowerTwist _ (-z) B.representation)) P ↔ _
  rw [realPowerTwist_cancel_neg, realPowerTwist_cancel_neg]

/-- The common-twist product formula transports through actual equivalences of
the two induced square-integrable families, at arbitrary positive total ranks. -/
theorem TemperedLFactorStatement.commonRealTwistsOfEquiv
    (H : TemperedLFactorStatement.{uF, uV, uW})
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (B : BlockShape m) (C : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin C.length → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (τ : ∀ j, Representation ℂ (GeneralLinear (C.size j) F.Carrier) (W j))
    (hiρ : ∀ i, Representation.IsIrreducible (ρ i))
    (hsρ : ∀ i, F.canonicalTopologicalData.IsSquareIntegrable (ρ i))
    (hiτ : ∀ j, Representation.IsIrreducible (τ j))
    (hsτ : ∀ j, F.canonicalTopologicalData.IsSquareIntegrable (τ j))
    {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
    {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']
    {γ : Representation ℂ (GeneralLinear m F.Carrier) V'}
    {δ : Representation ℂ (GeneralLinear n F.Carrier) W'}
    (a : (F.canonicalNormalizedProductInduced B ρ).Equiv γ)
    (b : (F.canonicalNormalizedProductInduced C τ).Equiv δ) (s z : ℝ) :
    ∃ (P : ℂ[X]) (Q : Fin B.length → Fin C.length → ℂ[X]),
      IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm m) s γ)
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) z δ) P ∧
      (∀ i j, IsPadicRankLPolynomial F ψ ν.val
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (B.size i)) s (ρ i))
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (C.size j)) z (τ j))
        (Q i j)) ∧
      P = ∏ i, ∏ j, Q i j := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst m n
  obtain ⟨P, Q, hP, hQ, hprod⟩ := H.commonRealTwists F ψ ν B C ρ τ hiρ hsρ hiτ hsτ s z
  let ea :=
    (F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv B
      (realTwistCharacter F s) ρ).symm.trans
        (twistEquiv (F.canonicalTopologicalData.determinantPowerCharacter (r + 1) s) a)
  let eb :=
    (F.canonicalTopologicalData.normalizedProductDeterminantTwistEquiv C
      (realTwistCharacter F z) τ).symm.trans
        (twistEquiv (F.canonicalTopologicalData.determinantPowerCharacter (t + 1) z) b)
  exact ⟨P, Q, (IsPadicSymmetricLPolynomial.congr_equiv ea eb).mp hP, hQ, hprod⟩

end Grouped

section Products

variable {I J A B : Type*} {K : A → Type*} {L : B → Type*}

/-- Pull a family of polynomials on the grouped indices back to the original
indices through the total-fiber equivalences. -/
def groupedPolynomial (E : (Σ a, K a) ≃ I) (G : (Σ b, L b) ≃ J)
    (R : ∀ a b, K a → L b → ℂ[X]) (i : I) (j : J) : ℂ[X] :=
  R (E.symm i).1 (G.symm j).1 (E.symm i).2 (G.symm j).2

theorem groupedPolynomial_apply (E : (Σ a, K a) ≃ I) (G : (Σ b, L b) ≃ J)
    (R : ∀ a b, K a → L b → ℂ[X]) (a : A) (b : B) (k : K a) (l : L b) :
    groupedPolynomial E G R (E ⟨a, k⟩) (G ⟨b, l⟩) = R a b k l := by
  exact congrArg₂ (fun (s : Σ a, K a) (t : Σ b, L b) => R s.1 t.1 s.2 t.2)
    (E.symm_apply_apply ⟨a, k⟩) (G.symm_apply_apply ⟨b, l⟩)

variable [Fintype I] [Fintype J] [Fintype A] [Fintype B]
  [∀ a, Fintype (K a)] [∀ b, Fintype (L b)]

/-- Reindex the four finite products by the total-fiber equivalences. -/
theorem prod_groupedPolynomial (E : (Σ a, K a) ≃ I) (G : (Σ b, L b) ≃ J)
    (R : ∀ a b, K a → L b → ℂ[X]) :
    (∏ a, ∏ b, ∏ k, ∏ l, R a b k l) = ∏ i, ∏ j, groupedPolynomial E G R i j := by
  classical
  calc
    _ = ∏ s : Σ a, K a, ∏ t : Σ b, L b, R s.1 t.1 s.2 t.2 := by
      simp only [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro a _
      exact Finset.prod_comm
    _ = _ := by
      rw [← E.prod_comp (fun i => ∏ j, groupedPolynomial E G R i j)]
      apply Finset.prod_congr rfl
      intro s _
      let v (x : Σ a, K a) (y : Σ b, L b) := R x.1 y.1 x.2 y.2
      change (∏ t, v s t) = ∏ j, v (E.symm (E s)) (G.symm j)
      simpa only [Equiv.symm_apply_apply] using
        G.prod_comp (fun j => v (E.symm (E s)) (G.symm j))

end Products

end Langlands.RankinSelberg
