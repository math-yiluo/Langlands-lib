import Langlands.Representation.Classification.UniformJacquetVanishing
import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof

/-!
# Derivative vanishing outside multiples of the cuspidal rank

The actual positive two-block Jacquet comparison turns the published
nondivisible-block vanishing into derivative vanishing for actual
subquotients of cuspidal products. No Leibniz formula is used.
-/

noncomputable section
open CategoryTheory

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- All proper positive derivative orders not divisible by `r` vanish. -/
def NondivisibleProperDerivativeVanishing {n : ℕ} (r : ℕ)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k : ℕ) (hk : k ≤ n), 0 < k → k < n → ¬ r ∣ k →
      Subsingleton
        ((Derivative.generalLinearDerivative.{uF,max uF uV} T ψ n k hk).obj π)

/-- A zero normalized positive two-block Jacquet module forces the
corresponding derivative to be zero. -/
theorem derivative_subsingleton_of_jacquet_subsingleton
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (a + b) F.Carrier)),
      Subsingleton ((T.normalizedJacquetFunctor
        (Shahidi.twoBlocks a b ha hb)).obj π) →
      Subsingleton ((Derivative.generalLinearDerivative.{uF,max uF uV}
        T ψ (a + b) b (Nat.le_add_left b a)).obj π) := by
  let := T.topology
  intro π hJ
  let J := (Derivative.positiveTwoBlockNormalizedJacquet.{uF,max uF uV}
    T a b ha hb).obj π
  have : Subsingleton J := hJ
  have hpartial : Subsingleton ((Derivative.partialDerivative T ψ a b).obj J) :=
    (Derivative.partialDerivativeMk_surjective T ψ a b J).subsingleton
  obtain ⟨E⟩ := Derivative.partialDerivativeJacquetComparison.{uF,max uF uV}
    F T ψ a b ha hb
  have hcast : Subsingleton
      ((Derivative.generalLinearRankCast T (Nat.add_sub_cancel a b)).obj
        ((Derivative.generalLinearDerivative T ψ (a + b) b
          (Nat.le_add_left b a)).obj π)) :=
    @Function.Injective.subsingleton _ _ _
      (SmoothRep.equivOfIso (E.app π)).injective hpartial
  have transport {m m' : ℕ} (h : m = m')
      (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier)) :
      Subsingleton ((Derivative.generalLinearRankCast T h).obj A) →
        Subsingleton A := by
    subst h
    exact id
  exact transport _ _ hcast

/-- The nondivisible-block Jacquet condition implies the corresponding
vanishing of proper positive derivatives. -/
theorem NondivisibleJacquetVanishing.derivatives
    {n r : ℕ}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : NondivisibleJacquetVanishing T r π) :
    NondivisibleProperDerivativeVanishing T r π := by
  let := T.topology
  intro ψ k hk hk0 hkn hdiv
  obtain ⟨a, rfl⟩ : ∃ a, n = a + k := ⟨n - k, by omega⟩
  have ha : 0 < a := by omega
  apply derivative_subsingleton_of_jacquet_subsingleton T ψ ha hk0 π
  exact hπ (Shahidi.twoBlocks a k ha hk0) ⟨1, hdiv⟩

/-- Every actual subquotient of a product of supercuspidal block factors has
zero derivative in any proper positive order not divisible by a common
divisor of the inducing block sizes. -/
theorem supercuspidal_product_subquotient_nondivisible_derivatives
    {n r : ℕ} (hn : 0 < n) (B : BlockShape n)
    (hB : ∀ i, r ∣ B.size i) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (Z : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      SmoothRep.IsSubquotient Z
        ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)) →
      NondivisibleProperDerivativeVanishing T r Z := by
  let := T.topology
  intro A Z hZ
  apply NondivisibleJacquetVanishing.derivatives T
  intro D hD
  exact supercuspidal_product_subquotient_jacquet_subsingleton_of_not_dvd
    T hn B D hB hD A Z hZ

/-- In particular the result holds for all actual subquotients of an
increasing segment induction. -/
theorem segment_induction_subquotient_nondivisible_derivatives
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r))
      (Z : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (m * r) F.Carrier)),
      SmoothRep.IsSubquotient Z (T.segmentInduced A.obj m hr) →
      NondivisibleProperDerivativeVanishing T r Z := by
  let := T.topology
  intro A Z hZ
  apply NondivisibleJacquetVanishing.derivatives T
  intro D hD
  exact segment_induction_subquotient_jacquet_subsingleton_of_not_dvd
    T hm hr D hD A Z hZ

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open Classification GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An actual segment quotient has no proper positive derivative outside
multiples of its cuspidal rank. -/
theorem IsSegmentQuotient.nondivisibleDerivatives
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentQuotient Δ π) :
    NondivisibleProperDerivativeVanishing T Δ.rank π := by
  let := T.topology
  obtain ⟨A, _, _, q, hq⟩ := hπ
  exact segment_induction_subquotient_nondivisible_derivatives T
    Δ.length_pos Δ.rank_pos A π
    (SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩)

/-- The strong head relation gives the same actual derivative vanishing. -/
theorem IsSegmentHead.nondivisibleDerivatives
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) :
    NondivisibleProperDerivativeVanishing T Δ.rank π :=
  hπ.isSegmentQuotient.nondivisibleDerivatives T

/-- For a length-two special head, the only possibly nonzero proper
positive derivative is the one of order equal to the cuspidal rank. -/
theorem IsSegmentHead.length_two_derivative_subsingleton
    {Δ : Segment.{uV,uF} T}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) (hΔ : Δ.length = 2)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k : ℕ) (hk : k ≤ Δ.degree) (hk0 : 0 < k) (hkn : k < Δ.degree)
    (hne : k ≠ Δ.rank) :
    letI := T.topology
    Subsingleton ((Derivative.generalLinearDerivative.{uF,max uF uV}
      T ψ Δ.degree k hk).obj π) := by
  let := T.topology
  apply hπ.nondivisibleDerivatives T ψ k hk hk0 hkn
  intro hdiv
  apply hne
  apply Nat.eq_of_dvd_of_lt_two_mul hk0.ne' hdiv
  simpa only [Segment.degree, hΔ] using hkn

end Langlands.PadicField.TopologicalData
