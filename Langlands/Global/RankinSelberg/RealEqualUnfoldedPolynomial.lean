import Langlands.Global.RankinSelberg.RealAdjacentSeparatedPolynomial
import Langlands.Global.RankinSelberg.RealGodementStandardGaussians
import Langlands.Global.RankinSelberg.RealMatrixCoefficientGrowth

/-! # Polynomial normalization of the unfolded real equal-rank integral -/

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open RealGodementGaussianPolynomial (Coordinates standardMatrixTest standardMatrixTest_apply
  scalePolynomial matrixSqNorm coordinates)
open RealSquarePolynomialGaussian
open RealEqualPolynomialGeneration (IsGaussianPolynomialRow)
open RealJacquet (realAdjacentMatrixWeight realMatrixZetaKernel_detCharacter
  realOrthogonalCompactProjectionPremise realLocalCompactProjectionReduction realPairLFactor_equal_pair)
open RealJacquetFrobenius (charData)

attribute [local instance] archimedeanEquationRealGLMeasurable archimedeanEquationRealGLBorel
  archimedeanEquationRealNMeasurable archimedeanEquationRealNBorel
  archimedeanEquationRealQMeasurable archimedeanEquationRealQBorel

variable {t : ℕ}

local notation "m" => (t + 1 : ℕ)
local notation "n" => (t + 2 : ℕ)
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear n ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Row" => Fin n → ℝ
local notation "gap" => Nat.lt_succ_self t
local notation "L[" ds "," es "]" => fun s : ℂ => ((realPairLFactor ds es).denominator s)⁻¹

/-- Joining a standard rectangular test and a standard Gaussian row gives a standard square
test, with the entry polynomial in the first rows times the polynomial in the last row. -/
theorem equalSquareSchwartz_standardMatrixTest (p : MvPolynomial (Coordinates m n) ℂ)
    (φ : 𝓢(Row, ℂ)) (hφ : IsGaussianPolynomialRow Real.pi φ) :
    ∃ q : MvPolynomial (Coordinates n n) ℂ,
      (equalSquareSchwartz (standardMatrixTest p) φ : Mat → ℂ) = squarePolynomialGaussian q := by
  obtain ⟨q, hq⟩ := hφ
  let i : Coordinates m n → Coordinates n n := fun j => (j.1.castSucc, j.2)
  let j : Fin n → Coordinates n n := fun k => (Fin.last m, k)
  refine ⟨rename i (scalePolynomial p) * rename j q, funext fun A => ?_⟩
  rw [equalSquareSchwartz_apply, equalSquareTest, standardMatrixTest_apply, hq,
    squarePolynomialGaussian, map_mul, eval_rename, eval_rename]
  have hN : matrixSqNorm A = matrixSqNorm (squareFirstRows A) + ∑ k, (A (Fin.last m) k) ^ 2 := by
    unfold matrixSqNorm
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hN, mul_add, Real.exp_add, Complex.ofReal_mul]
  change (_ * _) * (eval (coordinates A ∘ j) q *
      (Real.exp (-Real.pi * ∑ k, A (Fin.last m) k ^ 2) : ℂ)) =
    (eval (coordinates (squareFirstRows A)) (scalePolynomial p) * eval (coordinates A ∘ j) q) * _
  ring

/-- Given adjacent-rank polynomiality, an unfolded equal-rank kernel with a standard
square test has a polynomial normalization, with the leading real part prescribed by
joint absolute convergence. -/
def RealEqualUnfoldedPolynomialStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1))
    (a : ℝˣ), RealAdjacentPolynomialAtRank t (-a) →
    ∀ (e : Fin 2) (cs fs : List RealCharacterData), cs.length = m → fs.length = n →
    ∀ (U : G → ℂ), U ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a →
    ∀ (B : Automorphic.realStandardKFinite n (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    ∀ (f : Automorphic.realStandardKFinite n (fs.map RealBlock.character))
      (Ψ : 𝓢(Mat, ℂ)) (p : MvPolynomial (Coordinates n n) ℂ),
      (Ψ : Mat → ℂ) = squarePolynomialGaussian p →
    ∀ τ σ : ℝ,
      (∀ z s : ℂ, τ < z.re → σ < s.re →
        Integrable (equalUnfoldedKernel (charData e z) Ψ U (B f) s) (D.measure.prod D'.groupHaar)) →
    ∃ (R : ℂ → Polynomial ℂ) (β : ℝ), ∀ z s : ℂ, τ < z.re → 0 < z.re → β < s.re →
      (∫ x, equalUnfoldedKernel (charData e z) Ψ U (B f) s x ∂(D.measure.prod D'.groupHaar)) =
        (R z).eval s * L[RealBlock.character (charData e z) :: cs.map RealBlock.character, fs.map RealBlock.character] s

set_option maxHeartbeats 1400000 in
theorem realEqualUnfoldedPolynomial : RealEqualUnfoldedPolynomialStatement (t := t) := by
  intro D D' a hAdj e cs fs hcs hfs U hU B hB f Ψ p hp τ σ hJ
  let : D'.groupHaar.IsHaarMeasure := D'.groupHaar_isHaar
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  let d := charData e 0
  let ν : Measure O := Measure.haar
  let iK : O →* H := Unitary.toUnits
  have hiK : Continuous iK := continuous_unitary_toUnits
  have hmem (k : O) : iK k ∈ unitaryCompact ℝ n := k.property
  have hsurj (g : H) (hg : g ∈ unitaryCompact ℝ n) : ∃ k : O, iK k = g :=
    ⟨⟨g.val, hg⟩, Units.ext rfl⟩
  have hFin : FiniteDimensional ℂ (Submodule.span ℂ (range fun k : O =>
      fun A : Mat => Ψ ((iK k)⁻¹.val * A))) := by
    rw [hp]
    exact finiteDimensional_leftSquareGaussian iK hmem p
  obtain ⟨κ, hκ, hκfin, hRep⟩ := exists_realCompactMatrixWeight ν iK hiK d Ψ Ψ.continuous hFin
  choose v hv hV using fun g => realOrthogonalCompactProjectionPremise (t + 1) es (-a) κ hκ hκfin B hB f g
  obtain ⟨l, W, w, hW, hExp⟩ := realLocalCompactProjectionReduction (r := t + 1) iK hiK hmem hsurj
    es (-a) ν inferInstance κ hκ hκfin f B hB v hv (fun x g => hV g x)
  let C (j : Fin l) (g : H) : ℂ := ∫ k, w j k * (f : H → ℂ) (iK k * g) ∂ν
  let K (j : Fin l) (s : ℂ) (g : H) := realWeightedMatrixTest d Ψ (s + ((t : ℂ) + 1) / 2) g * C j g
  let Z (j : Fin l) (s : ℂ) := ∫ g, K j s g ∂D'.groupHaar
  have heK (j : Fin l) (s : ℂ) : K j s = fun g => realAdjacentMatrixWeight d.character.toMonoidHom Ψ s g * C j g := by
    funext g
    change realWeightedMatrixTest (charData e 0) Ψ (s + ((t : ℂ) + 1) / 2) g * C j g = _
    rw [realWeightedMatrixTest_mul_eq_zetaKernel e, realMatrixZetaKernel_detCharacter]
  have hM (j : Fin l) := realCompactSquarePolynomial (r := t + 1) D'.groupHaar iK hiK hmem ν
    (w j) (hW j).2 fs hfs d f.val f.2.1.1 Ψ p hp
  choose β M hM using hM
  obtain ⟨β₀, hβ₀⟩ := (finite_range β).bddAbove
  have hZ : ∃ β : ℝ, ∀ s : ℂ, β < s.re → ∀ j : Fin l, Integrable (K j s) D'.groupHaar ∧
      Z j s = ∫ g, K j s g ∂D'.groupHaar := by
    refine ⟨β₀, fun s hs j => ⟨?_, rfl⟩⟩
    rw [heK]
    exact (hM j s ((hβ₀ (mem_range_self j)).trans_lt hs)).1
  have hVf : B f ∈ realUniformWhittakerModel (t + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  obtain ⟨γ, hγ⟩ := realLocalEqualShiftedProducts_of_integrable (t := t) D D' O ν iK hiK
    (fun k => MaximalParabolicIntegration.abs_det_unitary ⟨iK k, hmem k⟩) κ hκ a e ds es U (B f)
    hU hVf Ψ hRep l W C Z (fun j => (hW j).1) (fun x g => (hExp x g).1) hZ τ σ hJ
  have hd : realRank ds = m := (realRank_map_character cs).trans hcs
  have he : realRank es = n := (realRank_map_character fs).trans hfs
  have hN (j : Fin l) := hAdj fs cs hfs hcs D
    (⟨W j, by rw [realWhittakerModels_eq (t + 1) es he]; exact (hW j).1⟩,
      ⟨U, by rw [neg_neg, realWhittakerModels_eq t ds hd]; exact hU⟩)
  choose N P hP using hN
  choose α hα using fun j => (N j).eq_on_right
  obtain ⟨α₀, hα₀⟩ := (finite_range α).bddAbove
  let R (z : ℂ) : Polynomial ℂ := ∑ j, P j * (M j).comp (Polynomial.X + Polynomial.C z)
  refine ⟨R, max γ (max α₀ β₀), fun z s hz hz0 hs => ?_⟩
  rw [hγ z s hz hz0 ((le_max_left _ _).trans_lt hs), Polynomial.eval_finsetSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs₁ := (hα₀ (mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  have hs₂ : β j < (s + z).re := by
    have h := (hβ₀ (mem_range_self j)).trans_lt ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    rw [Complex.add_re]
    linarith
  have hL : realUnequalIntegral gap D (W j) U s = (P j).eval s * L[es, ds] s := by
    simpa only [hP j, realOrdinaryUnequalTest] using hα j s hs₁
  have hR : Z j (s + z) = (M j).eval (s + z) * L[[RealBlock.character d], es] (s + z) := by
    unfold Z
    rw [heK]
    exact (hM j (s + z) hs₂).2
  have hFac := congrArg Inv.inv (realPairLFactor_equal_pair e z ds fs s)
  rw [mul_inv] at hFac
  change L[es, ds] s * L[[RealBlock.character d], es] (s + z) =
    L[RealBlock.character (charData e z) :: ds, es] s at hFac
  change realUnequalIntegral gap D (W j) U s * Z j (s + z) =
    (P j * (M j).comp (Polynomial.X + Polynomial.C z)).eval s *
      L[RealBlock.character (charData e z) :: ds, es] s
  rw [hL, hR, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, ← hFac]
  ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
