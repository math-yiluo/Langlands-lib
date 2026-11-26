import Langlands.Global.RankinSelberg.ComplexSquareZetaConvolution
import Langlands.Global.RankinSelberg.ComplexSquareZetaUnit
import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist

/-! # A nonzero polynomial square convolution at every spectral point -/

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ComplexCompactProfileFamily (characterList)
open ComplexDeterminantTwist (detCharacter detMul_apply detCharacter_inv_mul detMul_mem_kFiniteFunctions
  complexPositionCharacter_map_mul_inv)
open ComplexGodementGaussianPolynomial (Coordinates)
open ComplexGodement (normPower)
open ComplexSquareZeta (squarePolynomialGaussian zetaKernel complexSquareZetaUnit)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {r : ℕ}
local notation "n" => (r + 1 : ℕ)
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "KF[" e "]" => complexStandardKFinite n (List.ofFn e)

private theorem singleton_pairFactor (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData) :
    complexLFactor (List.ofFn fun j => (e j).mul d) = complexPairLFactor [d] (List.ofFn e) := by
  apply ReciprocalEntire.ext
  funext s
  simp only [complexPairLFactor, complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_ofFn, denominator_complexLFactor, List.prod_ofFn, Function.comp_apply,
    ComplexCharacterData.lFactor, ComplexCharacterData.mul, add_comm d.weight, add_comm d.exponent]

/-- The group determinant power is the corresponding power of the norm on `ℂˣ`. -/
theorem square_detPower_eq_normPower (g : G) (s : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g s = normPower s (determinant g) := by
  have hp : 0 < complexNormalizedAbs g.val.det := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  change Complex.exp (s * (Real.log (complexNormalizedAbs g.val.det) : ℂ)) =
    ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le,
    mul_comm]

/-- Scalar evaluations of a finite polynomial family of inducing vectors are entire. -/
theorem differentiable_squareConvolution_evaluation {μ : Measure G} {d : ComplexCharacterData}
    {e : Fin n → ComplexCharacterData} {Φ : 𝓢(Mat, ℂ)} {f : KF[e]} {F : ℂ → KF[e]}
    (hF : IsComplexSquareConvolution μ d e Φ f F) (b : KF[e] →ₗ[ℂ] ℂ) :
    Differentiable ℂ (fun s => b (F s)) := by
  obtain ⟨l, p, v, h⟩ := hF.1
  simp_rw [h, map_sum, map_smul, smul_eq_mul]
  exact fun s => DifferentiableAt.fun_sum fun j _ => (p j).differentiable.differentiableAt.mul_const _

/-- For an ordered list of angular weights, a square polynomial Gaussian convolution has
constant nonzero inducing value at the identity and the usual Whittaker convolution formula. -/
def ComplexSquareConvolutionUnitStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (d : ComplexCharacterData) (e : Fin n → ComplexCharacterData),
    Monotone (fun j => (e j).weight) →
    ∀ (a : ℂˣ) (B : KF[e] →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r (List.ofFn e) a B →
    ∃ (Φ : 𝓢(Mat, ℂ)) (P : MvPolynomial (Coordinates n n) ℂ) (f : KF[e])
      (F : ℂ → KF[e]) (c : ℂ),
      (Φ : Mat → ℂ) = squarePolynomialGaussian P ∧
      IsComplexSquareConvolution μ d e Φ f F ∧ c ≠ 0 ∧ (∀ s, (F s).val 1 = c) ∧
      ∃ σ : ℝ, ∀ (s : ℂ), σ < s.re → ∀ x : G,
        B (F s) x = (complexPairLFactor [d] (List.ofFn e)).denominator s *
          ∫ g, complexJacquetMatrixIntegrand d (fun g => B f (x * g)) Φ s g ∂μ

set_option maxHeartbeats 800000 in
theorem complexSquareConvolutionUnit : ComplexSquareConvolutionUnitStatement (r := r) := by
  intro μ hμ d e hm a B hB
  let w (j : Fin n) := ((e j).mul d).weight
  let p (j : Fin n) := ((e j).mul d).exponent
  have hw : Monotone w := fun i j h => add_le_add_left (hm h) _
  have ht : characterList w p = (List.ofFn e).map (fun z => z.mul d) := by
    rw [List.map_ofFn]
    unfold characterList
    congr 1
    funext j
    exact characterOfParams_eta ((e j).mul d)
  obtain ⟨Φ, P, u, c, σ, hΦ, hc, hZ⟩ := complexSquareZetaUnit (Nat.succ_pos r) μ w p hw
  let f : KF[e] := ⟨ComplexDeterminantTwist.detMul d.character⁻¹ u.val,
    detMul_mem_kFiniteFunctions d.character⁻¹
      (fun i z => by
        rw [ht]
        exact complexPositionCharacter_map_mul_inv d (List.ofFn e) List.length_ofFn i z) u.2⟩
  have hf (g : G) : detCharacter d.character g * f.val g = u.val g := by
    change detCharacter d.character g * (ComplexDeterminantTwist.detMul d.character⁻¹ u.val g) = _
    rw [detMul_apply, ← mul_assoc, mul_comm (detCharacter d.character g), detCharacter_inv_mul, one_mul]
  have hK (s : ℂ) (g : G) : complexJacquetMatrixIntegrand d f.val Φ s g = zetaKernel Φ u.val s g := by
    have hs : ((n : ℂ) - 1) / 2 = (r : ℂ) / 2 := by push_cast; ring
    rw [complexJacquetMatrixIntegrand, zetaKernel, hs, square_detPower_eq_normPower, ← hf g]
    change _ * detCharacter d.character g * _ * _ = _
    ring
  obtain ⟨F, hF, hV⟩ := complexSquareZetaConvolution μ d e Φ P hΦ a B hB f
  refine ⟨Φ, P, f, F, c, hΦ, hF, hc, ?_, hV⟩
  let ev := (LinearMap.proj (1 : G)).comp (complexStandardKFinite n (List.ofFn e)).subtype
  change ∀ s, ev (F s) = c
  obtain ⟨τ, hFτ⟩ := hF.2
  let b := max τ σ
  let s₁ : ℂ := ((b + 1 : ℝ) : ℂ)
  have hnear : ∀ᶠ s : ℂ in 𝓝 s₁, b < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [s₁])
  have hEq : (fun s => ev (F s)) = fun _ : ℂ => c := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (fun s _ => (differentiable_squareConvolution_evaluation hF ev).analyticAt s)
      (fun _ _ => analyticAt_const) (z₀ := s₁)
    filter_upwards [hnear] with s hs
    change (F s).val 1 = c
    rw [hFτ s ((le_max_left τ σ).trans_lt hs)]
    simp_rw [hK]
    rw [← singleton_pairFactor]
    have hList : (List.ofFn fun j => (e j).mul d) = characterList w p := by
      rw [ht, List.map_ofFn]
      rfl
    rw [hList]
    exact (hZ s ((le_max_right τ σ).trans_lt hs)).2
  exact congrFun hEq

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
