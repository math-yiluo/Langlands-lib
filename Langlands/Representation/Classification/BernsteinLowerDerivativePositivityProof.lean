import Langlands.Representation.Classification.BernsteinLowerDerivativePositivityStatement
import Langlands.Representation.Classification.BernsteinDerivativeEigenvector
import Langlands.Representation.Derivative.MirabolicPhiMinusUnitarityProof
import Langlands.Representation.Derivative.MirabolicRadicalContraction
import Langlands.Representation.Derivative.MirabolicHomogeneousDescent

/-!
# Lower shifted-derivative positivity for irreducible unitary representations

Bernstein 1984, §7.3–7.4: for an irreducible unitarizable representation `π` of
`GL_N(F)` with highest derivative of order `h`, every irreducible subquotient of
`ν^(1/2) π^(k)`, `k < h`, has positive central exponent. The order-zero case is the
unitarity of the scalar action. For `k = k' + 1`, the derivative is
`ν^(1/2) Ψ⁻ τ` with `τ = (Φ⁻)^k' (π|P)`. Here `τ` is unitarizable (iterating
`MirabolicPhiMinusUnitarity`) and has no nonzero radical-fixed vector (homogeneity
of `π|P` descends through `Φ⁻`), so radical averaging contracts uniformizer
eigenvalues on its radical coinvariants.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Iterated normalized `Φ⁻` preserves unitarizability. -/
theorem isUnitarizable_phiMinusIterate
    (hU : MirabolicPhiMinusUnitarity.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (j : ℕ) (B : SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + j) F.Carrier)),
      IsUnitarizable B.representation →
        IsUnitarizable ((phiMinusIterate T ψ n j).obj B).representation := by
  let := T.topology
  intro j
  induction j with
  | zero => exact fun B hB => hB
  | succ j ih =>
    intro B hB
    exact ih ((Mirabolic.phiMinus T ψ (n + j)).obj B) (hU ψ (n + j) B hB)

/-- The mirabolic restriction of a unitarizable representation is unitarizable. -/
theorem isUnitarizable_generalLinearRestriction {N : ℕ} :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      IsUnitarizable π.representation →
        IsUnitarizable ((generalLinearRestriction T N).obj π).representation := by
  let := T.topology
  rintro π ⟨b⟩
  exact ⟨{ toInnerProductCore := b.toInnerProductCore
           invariant := fun g => b.invariant (g : GeneralLinear (N + 1) F.Carrier) }⟩

/-- Positive orders of Bernstein's lower positivity: for `π` irreducible and
unitarizable on `GL_a`, `a = n + k' + 1`, with a nonzero derivative of order
`h > k' + 1`, the admissible shifted derivative `ν^(1/2) π^(k'+1)` has positive
central exponents. The rank is generic so that the rank cast can be eliminated. -/
theorem bernsteinPositiveCentralExponents_succ
    (hU : MirabolicPhiMinusUnitarity.{uF, uV} F T)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a n k' : ℕ}
    (ha : a = n + k' + 1) (hn : 0 < n)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (hunit : letI := T.topology; IsUnitarizable π.representation)
    {h : ℕ} (hh : h ≤ a) (hkh : k' + 1 < h)
    (hnz : letI := T.topology; Nontrivial ((generalLinearDerivative T ψ a h hh).obj π))
    (hadm : letI := T.topology
      (T.segmentFactor ((generalLinearDerivativePositive T ψ n k').obj
        ((generalLinearRankCast T ha).obj π)) (1 / 2)).IsAdmissible) :
    BernsteinPositiveCentralExponents T
      (T.segmentFactor ((generalLinearDerivativePositive T ψ n k').obj
        ((generalLinearRankCast T ha).obj π)) (1 / 2)) := by
  let := T.topology
  subst ha
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let R := (generalLinearRestriction T (m + 1 + k')).obj π
  let τ := (phiMinusIterate T ψ (m + 1) k').obj R
  have hlevR : h ≤ level T ψ R :=
    le_level_of_hasNonzeroDerivative T ψ R
      ((Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff F T ψ
        ⟨by omega, hh⟩ π).mpr hnz)
  have hR : IsHomogeneous T ψ R :=
    Mirabolic.isHomogeneous_restriction_of_isIrreducible T ψ π hirr
  obtain ⟨hτ, hlevτ⟩ :=
    Mirabolic.isHomogeneous_phiMinusIterate T ψ (m + 1) k' R hR (by omega)
  have hlevτ' : level T ψ τ + k' = level T ψ R := hlevτ
  have hfix := Mirabolic.eq_zero_of_radical_fixed T ψ (M := m) τ hτ (by omega)
  have hτu : IsUnitarizable τ.representation :=
    isUnitarizable_phiMinusIterate F T hU ψ (m + 1) k' R
      (isUnitarizable_generalLinearRestriction F T π hunit)
  exact bernsteinPositiveCentralExponents_segmentFactor_psiMinus T τ hadm
    (Mirabolic.norm_lt_one_of_radical_eigen T m τ.representation τ.isSmooth hτu hfix)

/-- Bernstein's lower shifted-derivative positivity, assuming that normalized
mirabolic `Φ⁻` preserves unitarizability. -/
theorem bernsteinUnitaryLowerDerivativePositivity_of_phiMinusUnitarity
    (hU : MirabolicPhiMinusUnitarity.{uF, uV} F T) :
    BernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T := by
  let := T.topology
  intro N hN ψ π hirr hunit hd k hk hkh
  cases k with
  | zero => exact bernsteinShiftedDerivative_zero_positive F T hN ψ π hirr hunit hk
  | succ k' =>
    exact bernsteinPositiveCentralExponents_succ F T hU ψ (rank_eq_of_succ_le hk)
      (by have := hd.le_rank; omega) π hirr hunit hd.le_rank hkh hd.nonzero
      (bernsteinShiftedDerivative_isAdmissible F T ψ π hirr (k' + 1) hk)

/-- Bernstein's lower shifted-derivative positivity (Bernstein 1984, §7.4, with the
order-zero case of §8.2) for irreducible unitarizable representations of `GL_N(F)`. -/
theorem bernsteinUnitaryLowerDerivativePositivity :
    BernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T :=
  bernsteinUnitaryLowerDerivativePositivity_of_phiMinusUnitarity F T
    (Mirabolic.mirabolicPhiMinusUnitarity.{uF, uV} F T)

end Langlands.Classification
