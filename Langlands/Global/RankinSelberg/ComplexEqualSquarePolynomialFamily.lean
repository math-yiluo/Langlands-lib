import Langlands.Global.RankinSelberg.ComplexLocalEqualFiniteSquareNormalized
import Langlands.Global.RankinSelberg.ComplexOrdinaryAdjacentPolynomial

/-! # Polynomial products in the equal-rank square unfolding -/

noncomputable section

open MeasureTheory Set
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz)
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Archimedean.ComplexDuality
open Langlands.GeneralLinear Langlands.Automorphic Langlands.GodementJacquet
open Langlands.LocalFactor.Archimedean
open ComplexGodement (shiftedCharacter)
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexSquareZeta (squarePolynomialGaussian finiteDimensional_leftSquarePolynomialGaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "μK" => unitaryHaar n
local notation "gap" => Nat.lt_succ_self r

private theorem matrixPolynomial_of_compactBorel [mK : MeasurableSpace K] [BorelSpace K]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsHaarMeasure] [IsFiniteMeasure ν]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (f : complexStandardKFinite n (List.ofFn e)) (w : K → ℂ) (hw : Continuous w)
    (Φ : OperatorSchwartz n n) (p : MvPolynomial (Coordinates n n) ℂ)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian p) :
    let b (g : G) := ∫ k, w k * f.val (k.val * g) ∂ν
    ∃ (σ : ℝ) (P : Polynomial ℂ), ∀ s : ℂ, σ < s.re →
      Integrable (complexJacquetMatrixIntegrand d b Φ s) μ ∧
      P.eval s = (complexPairLFactor [d] (List.ofFn e)).denominator s *
        ∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ := by
  have hK : mK = (Subtype.instMeasurableSpace : MeasurableSpace K) := by
    trans borel K
    · exact BorelSpace.measurable_eq
    · symm
      exact @BorelSpace.measurable_eq K _ Subtype.instMeasurableSpace (Subtype.borelSpace _)
  subst mK
  obtain ⟨σ, P, _, hP⟩ := complexLocalMatrixPolynomial (r := r + 1) μ ν d e f.val f.2.1 w hw Φ p hΦ
  exact ⟨σ, P, hP⟩

/-- On the positive adjoining-exponent chamber, the unfolded equal-rank integral of a
standard square polynomial Gaussian has polynomial spectral fibers if adjacent ordinary
normalizations are polynomial. -/
def ComplexEqualSquarePolynomialFamilyStatement : Prop :=
  ∀ (a : ℂˣ), ComplexAdjacentPolynomialAtRank r (-a) →
    ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
      (d : ComplexCharacterData) (ds : List ComplexCharacterData), ds.length = m →
    ∀ (e : Fin n → ComplexCharacterData) (U : complexWhittakerModel r ds a)
      (B : complexStandardKFinite n (List.ofFn e) →ₗ[ℂ] (G → ℂ)),
      IsComplexWhittakerIntertwiner (r + 1) (List.ofFn e) (-a) B →
    ∀ (f : complexStandardKFinite n (List.ofFn e)) (Ψ : OperatorSchwartz n n)
      (p : MvPolynomial (Coordinates n n) ℂ), (Ψ : Mat → ℂ) = squarePolynomialGaussian p →
      ∃ (P : ℂ → Polynomial ℂ) (τ σ : ℝ), ∀ z s : ℂ, τ < z.re → σ < s.re →
        (P z).eval s = equalDoubleDenominator d ds (List.ofFn e) z s *
          complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d z).character.toMonoidHom
            Ψ U.val (B f) s

set_option maxHeartbeats 1200000 in
theorem complexEqualSquarePolynomialFamily : ComplexEqualSquarePolynomialFamilyStatement (r := r) := by
  intro a hAdj D D₁ d ds hds e U B hB f Ψ p hΨ
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let es := List.ofFn e
  let V : complexWhittakerModel (r + 1) es (-a) :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let η : ℂˣ →* ℂˣ := d.character
  obtain ⟨w, hw, hwfin, hRec⟩ := complexLocalCompactMatrixWeight μK inferInstance
    (η.comp invMonoidHom) (d.character.continuous.comp continuous_inv) Ψ Ψ.continuous
    (finiteDimensional_leftSquarePolynomialGaussian Ψ p hΨ)
  obtain ⟨u, hu, hu'⟩ := complexLocalCompactMatchedProjection (r := r + 1) es (-a) μK
    inferInstance w hw hwfin B hB f
  obtain ⟨l, Vj, wj, hV, hExp⟩ := complexLocalCompactProjectionReduction (r := r + 1) es (-a)
    μK inferInstance w hw hwfin f B hB u hu hu'
  let bj (j : Fin l) (g : G) := ∫ k, wj j k * f.val (k.val * g) ∂μK
  let Z (j : Fin l) (s : ℂ) := ∫ g, complexJacquetMatrixIntegrand d (bj j) Ψ s g ∂D.groupHaar
  choose β Q hQ using fun j => matrixPolynomial_of_compactBorel D.groupHaar μK d e f (wj j) (hV j).2 Ψ p hΨ
  obtain ⟨β₀, hβ⟩ := (Set.finite_range β).bddAbove
  have hZ : ∃ β₀ : ℝ, ∀ t : ℂ, β₀ < t.re → ∀ j,
      let F := fun g => complexWeightedMatrixTest d.character Ψ (t + ((m : ℕ) : ℂ) / 2) g * bj j g
      Integrable F D.groupHaar ∧ Z j t = ∫ g, F g ∂D.groupHaar := by
    exact ⟨β₀, fun t ht j => ⟨(hQ j t ((hβ (Set.mem_range_self j)).trans_lt ht)).1, rfl⟩⟩
  obtain ⟨τ, σ, hProd⟩ := complexLocalEqualShiftedProducts D D₁ μK (MonoidHom.id K)
    continuous_id w hw a d ds es U V Ψ hRec l Vj bj Z (fun j => (hV j).1)
    (fun x g => (hExp x g).1) hZ
  let U' : complexWhittakerModel r ds (-(-a)) := ⟨U, by simpa only [neg_neg] using U.2⟩
  choose N P hP using fun j => hAdj es ds List.length_ofFn hds D₁ ⟨Vj j, (hV j).1⟩ U'
  choose σj hσj using fun j => (N j).eq_on_right
  obtain ⟨σ₀, hσ₀⟩ := (Set.finite_range σj).bddAbove
  obtain ⟨σL, hσL⟩ := FunctionalEquationComparison.CompletedEquationAdapter.complexPairLFactor_denominator_ne_zero es ds
  let R (z : ℂ) : Polynomial ℂ := ∑ j, P j * (Q j).comp (Polynomial.X + Polynomial.C z)
  refine ⟨R, max τ 0, max (max σ σ₀) (max β₀ σL), fun z s hz hs => ?_⟩
  have hsp : σ < s.re := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hs)
  have hsz : β₀ < (s + z).re := by
    rw [Complex.add_re]
    linarith [((le_max_left β₀ σL).trans_lt ((le_max_right _ _).trans_lt hs) : β₀ < s.re),
      (le_max_right τ 0).trans_lt hz]
  have hL := hσL s ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  change _ = equalDoubleDenominator d ds es z s *
    complexEqualUnfoldedIntegral D.groupHaar D₁ (shiftedCharacter d z).character Ψ U.val V.val s
  rw [hProd z s ((le_max_left _ _).trans_lt hz) hsp, Finset.mul_sum]
  simp only [R, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : σj j < s.re := (hσ₀ (Set.mem_range_self j)).trans_lt
    ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hs))
  have hEq : complexUnequalIntegral gap D₁ (Vj j) U.val s =
      (P j).eval s * ((complexPairLFactor es ds).denominator s)⁻¹ := by
    have he := hσj j s hj
    rw [congrFun (hP j) s] at he
    exact he
  have hQeq : (Q j).eval (s + z) = (complexPairLFactor [d] es).denominator (s + z) * Z j (s + z) :=
    (hQ j (s + z) ((hβ (Set.mem_range_self j)).trans_lt hsz)).2
  rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    hQeq, hEq, equalDoubleDenominator]
  field_simp [hL]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
