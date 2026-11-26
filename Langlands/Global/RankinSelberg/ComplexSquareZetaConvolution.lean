import Langlands.Global.RankinSelberg.ComplexLocalMatrixEquation
import Langlands.Global.RankinSelberg.ComplexLocalMatrixMajorant
import Langlands.Global.RankinSelberg.ComplexLocalCompactAveraging
import Langlands.Global.RankinSelberg.ComplexLocalCompactMatchedProjection

/-! # Polynomial convolution by complex square Gaussian tests -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open ComplexGodement (exists_height_bound_standard)
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexSquareZeta (squarePolynomialGaussian finiteDimensional_leftSquarePolynomialGaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "KU" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "KF[" e "]" => complexStandardKFinite n (List.ofFn e)
local notation "κ" => ComplexDuality.unitaryHaar n

private theorem matrixPolynomial_unitaryHaar (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (f : KF[e]) (w : KU → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ))
    (P : MvPolynomial (Coordinates n n) ℂ) (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) :
    let b (g : G) := ∫ k, w k * f.val (k.val * g) ∂κ
    ∃ (σ : ℝ) (p : Polynomial ℂ), ∀ s : ℂ, σ < s.re →
      Integrable (complexJacquetMatrixIntegrand d b Φ s) μ ∧
      p.eval s = (complexPairLFactor [d] (List.ofFn e)).denominator s *
        ∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ := by
  have tr [mK : MeasurableSpace KU] [BorelSpace KU] (ν : Measure KU) [ν.IsHaarMeasure] [IsFiniteMeasure ν] :
      let b (g : G) := ∫ k, w k * f.val (k.val * g) ∂ν
      ∃ (σ : ℝ) (p : Polynomial ℂ), ∀ s : ℂ, σ < s.re →
        Integrable (complexJacquetMatrixIntegrand d b Φ s) μ ∧
        p.eval s = (complexPairLFactor [d] (List.ofFn e)).denominator s *
          ∫ g, complexJacquetMatrixIntegrand d b Φ s g ∂μ := by
    have hK : mK = (Subtype.instMeasurableSpace : MeasurableSpace KU) := by
      trans borel KU
      · exact BorelSpace.measurable_eq
      · symm
        exact @BorelSpace.measurable_eq KU _ Subtype.instMeasurableSpace (Subtype.borelSpace _)
    subst mK
    obtain ⟨σ, p, _, hp⟩ := complexLocalMatrixPolynomial μ ν d e f.val f.2.1 w hw Φ P hΦ
    exact ⟨σ, p, hp⟩
  exact tr κ

private theorem compact_reproduce_integral (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ]
    (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (w : KU → ℂ) (hw : Continuous w)
    (hRec : ∀ X, ∫ k, w k * complexCompactMatrixTranslate
      (d.character.toMonoidHom.comp invMonoidHom) Φ k X ∂κ = Φ X)
    (b : G → ℂ) (hb : Continuous b) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ g, ‖b g‖ ≤ C * complexMatrixHeight g ^ N) (s : ℂ)
    (hs : (n : ℝ) + N ≤ (s + (r : ℂ) / 2 + d.exponent).re) (x : G) :
    let A := complexWeightedMatrixTest d.character Φ (s + (r : ℂ) / 2)
    (∫ g, A g * b (x * g) ∂μ) =
      ∫ g, A g * (∫ k, w k * b (x * k.val * g) ∂κ) ∂μ := by
  intro A
  let K₀ := (unitaryCompact ℂ n).subtype
  have hK₀ : Measurable K₀ := continuous_subtype_val.measurable
  let F (g : G) := b (x * g)
  have hA := complexWeightedMatrixTest_reproduce (r := r) id κ d.character Φ w hRec (s + (r : ℂ) / 2)
  apply Eq.trans (integral_of_compact_average K₀ hK₀ κ μ w A F (fun g => hA g) ?_)
  · simp only [F, K₀, Subgroup.subtype_apply, mul_assoc]
  apply (integrable_compact_average_iff K₀ hK₀ κ μ w A F).mpr
  let H (g : G) := max 1 (complexMatrixHeight g)
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hw.continuousOn
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((continuous_const.max continuous_complexMatrixHeight).comp
      (continuous_const.mul continuous_subtype_val : Continuous fun k : KU => x * k.val)).continuousOn
  let M := max D 0 * (C * max L 0 ^ N)
  have hMajor := complexLocalMatrixMajorant n N μ d Φ (s + (r : ℂ) / 2) hs
  have hCont : Continuous A := (((Φ.continuous.comp Units.continuous_val).mul
    (Units.continuous_val.comp (d.character.continuous.comp continuous_complexDeterminant))).mul
      (continuous_complexDetPower _))
  have hF : Continuous (fun p : KU × G => A p.2 * (w p.1 * F (K₀ p.1 * p.2))) :=
    (hCont.comp continuous_snd).mul ((hw.comp continuous_fst).mul
      (hb.comp (continuous_const.mul ((continuous_subtype_val.comp continuous_fst).mul continuous_snd))))
  refine (((hMajor.const_mul M).comp_snd κ).mono' hF.aestronglyMeasurable (ae_of_all _ fun p => ?_))
  have h₁ : ‖w p.1‖ ≤ max D 0 := (hD p.1 (mem_univ _)).trans (le_max_left _ _)
  have h₂ : H (x * p.1.val) ≤ max L 0 := by
    exact (le_abs_self _).trans ((hL p.1 (mem_univ _)).trans (le_max_left _ _))
  have h₃ : ‖b (x * p.1.val * p.2)‖ ≤ C * max L 0 ^ N * H p.2 ^ N := by
    refine (hBound _).trans ?_
    rw [mul_assoc C, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (complexMatrixHeight_nonneg _)
      ((le_max_right 1 _).trans ((max_complexMatrixHeight_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right h₂ (zero_le_one.trans (le_max_left _ _))))) _) hC
  change ‖A p.2 * (w p.1 * b (x * (p.1.val * p.2)))‖ ≤ M * (H p.2 ^ N * ‖A p.2‖)
  rw [norm_mul, norm_mul, ← mul_assoc x]
  calc
    _ ≤ ‖A p.2‖ * (max D 0 * (C * max L 0 ^ N * H p.2 ^ N)) := by gcongr
    _ = _ := by dsimp only [M]; ring

/-- A polynomial vector-valued normalization of square convolution. -/
def IsComplexSquareConvolution (μ : Measure G) (d : ComplexCharacterData)
    (e : Fin n → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : KF[e]) (F : ℂ → KF[e]) : Prop :=
  (∃ (l : ℕ) (p : Fin l → Polynomial ℂ) (v : Fin l → KF[e]),
    ∀ s, F s = ∑ j, (p j).eval s • v j) ∧
  (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
    (F s).val 1 = (complexPairLFactor [d] (List.ofFn e)).denominator s *
      ∫ g, complexJacquetMatrixIntegrand d f.val Φ s g ∂μ)

/-- There is a polynomial output in the compact-finite standard module for every standard
square Gaussian convolution. Its Whittaker evaluation is the normalized convolution of the
input Whittaker function on a common right half-plane for all group arguments. -/
def ComplexSquareZetaConvolutionStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData)
    (Φ : 𝓢(Mat, ℂ)) (P : MvPolynomial (Coordinates n n) ℂ),
    (Φ : Mat → ℂ) = squarePolynomialGaussian P →
    ∀ (a : ℂˣ) (B : KF[e] →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r (List.ofFn e) a B →
    ∀ f : KF[e], ∃ F : ℂ → KF[e], IsComplexSquareConvolution μ d e Φ f F ∧
      ∃ σ : ℝ, ∀ (s : ℂ), σ < s.re → ∀ x : G,
        B (F s) x = (complexPairLFactor [d] (List.ofFn e)).denominator s *
          ∫ g, complexJacquetMatrixIntegrand d (fun g => B f (x * g)) Φ s g ∂μ

set_option maxHeartbeats 1500000 in
theorem complexSquareZetaConvolution : ComplexSquareZetaConvolutionStatement (r := r) := by
  intro μ hμ d e Φ P hΦ a B hB f
  let e₀ := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n
  let : LocallyCompactSpace G := e₀.locallyCompactSpace
  let : SecondCountableTopology G := e₀.secondCountableTopology
  let : SFinite μ := inferInstance
  let : CompactSpace KU := ComplexDuality.compactSpace_unitaryCompact n
  let ds := List.ofFn e
  obtain ⟨w, hw, hwFin, hRec⟩ := complexLocalCompactMatrixWeight κ inferInstance
    (d.character.toMonoidHom.comp invMonoidHom) (d.character.continuous.comp continuous_inv) Φ Φ.continuous
    (finiteDimensional_leftSquarePolynomialGaussian Φ P hΦ)
  obtain ⟨u, hu, hBu⟩ := complexLocalCompactMatchedProjection (r := r) ds a κ inferInstance w hw hwFin B hB f
  let ρ : KF[e] →ₗ[ℂ] (KU → ℂ) :=
    { toFun v k := v.val k.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hρ : Function.Injective ρ := by
    intro v v' h
    apply Subtype.ext
    exact ComplexPrincipalSeriesExtension.eq_of_eqOn_unitary v.2.1 v'.2.1
      (fun k hk => congrFun h ⟨k, hk⟩)
  have hf : Continuous f.val := f.2.1.1.continuous
  obtain ⟨l, v, wj, hwj, hExpanded⟩ := exists_compactPairing_expansion κ (unitaryCompact ℂ n).subtype
    f.val (fun g => hf.comp (continuous_subtype_val.mul continuous_const)) w hw
    (hasFiniteCompactConvolutionKernel_of_finite_translates w hw hwFin) ρ hρ u hu
  choose σj p hTrace using fun j => matrixPolynomial_unitaryHaar μ d e f (wj j) (hwj j) Φ P hΦ
  obtain ⟨σ₀, hσ₀⟩ := (finite_range σj).bddAbove
  let F (s : ℂ) : KF[e] := ∑ j, (p j).eval s • v j
  obtain ⟨M, hM⟩ := exists_height_bound_standard (Nat.succ_pos r) ds List.length_ofFn
  obtain ⟨C, hC, hC'⟩ := hM f.val f.2.1
  obtain ⟨D, N, hN⟩ := hB.2.2.1 f
  let γ := (((r : ℕ) : ℂ) / 2 + d.exponent).re
  let σ := max σ₀ (max ((n : ℝ) + M - γ) ((n : ℝ) + N - γ))
  let A (s : ℂ) := complexWeightedMatrixTest d.character Φ (s + (r : ℂ) / 2)
  let L s := (complexPairLFactor [d] ds).denominator s
  have hParts (s : ℂ) (hs : σ < s.re) (b : KF[e] →ₗ[ℂ] ℂ) :
      b (F s) = L s * ∫ g, A s g * b (u g) ∂μ := by
    let J (j : Fin l) (g : G) := ∫ k, wj j k * f.val (k.val * g) ∂κ
    have hJ (j : Fin l) := hTrace j s
      ((hσ₀ (mem_range_self j)).trans_lt ((le_max_left _ _).trans_lt hs))
    have he (g : G) : A s g * b (u g) = ∑ j, b (v j) * (A s g * J j g) := by
      rw [hExpanded g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      change A s g * (J j g * b (v j)) = _
      ring
    simp_rw [he]
    rw [integral_finsetSum]
    · simp only [F, map_sum, map_smul, smul_eq_mul, integral_const_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hpj : (p j).eval s = L s * ∫ g, A s g * J j g ∂μ := (hJ j).2
      rw [hpj]
      ring
    · exact fun j _ => ((hJ j).1 : Integrable (fun g => A s g * J j g) μ).const_mul _
  refine ⟨F, ⟨⟨l, p, v, fun _ => rfl⟩, ⟨σ, ?_⟩⟩, σ, ?_⟩
  · intro s hs
    let ev := (LinearMap.proj (1 : G)).comp (complexStandardKFinite n ds).subtype
    have hE (g : G) : ev (u g) = ∫ k, w k * f.val (k.val * g) ∂κ := by
      change (u g).val (1 : G) = _
      simpa only [OneMemClass.coe_one, one_mul] using hu g (1 : KU)
    have hBound : (n : ℝ) + M ≤ (s + (r : ℂ) / 2 + d.exponent).re := by
      have hh := (le_max_left ((n : ℝ) + M - γ) _).trans_lt ((le_max_right σ₀ _).trans_lt hs)
      rw [Complex.add_re, Complex.add_re]
      dsimp only [γ] at hh
      simp only [Complex.add_re] at hh
      linarith
    change ev (F s) = L s * _
    rw [hParts s hs ev]
    congr 1
    change (∫ g, A s g * ev (u g) ∂μ) = _
    simp_rw [hE]
    change (∫ g, A s g * (∫ k, w k * f.val (k.val * g) ∂κ) ∂μ) = ∫ g, A s g * f.val g ∂μ
    simpa only [one_mul, A] using
      (compact_reproduce_integral μ d Φ w hw hRec f.val hf M C hC hC' s hBound 1).symm
  · intro s hs x
    let ev := (LinearMap.proj x).comp B
    have hBound : (n : ℝ) + N ≤ (s + (r : ℂ) / 2 + d.exponent).re := by
      have hh := (le_max_right ((n : ℝ) + M - γ) _).trans_lt ((le_max_right σ₀ _).trans_lt hs)
      rw [Complex.add_re, Complex.add_re]
      dsimp only [γ] at hh
      simp only [Complex.add_re] at hh
      linarith
    change ev (F s) = L s * _
    rw [hParts s hs ev]
    congr 1
    have hE (g : G) : ev (u g) = ∫ k, w k * B f (x * k.val * g) ∂κ := hBu x g
    simp_rw [hE]
    exact (compact_reproduce_integral μ d Φ w hw hRec (B f) (hB.2.1 f).continuous
      N (max D 0) (le_max_right _ _) (fun g => (hN g).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (complexMatrixHeight_nonneg _) _)))
      s hBound x).symm

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
