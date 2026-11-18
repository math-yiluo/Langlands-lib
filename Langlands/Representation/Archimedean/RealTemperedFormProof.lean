import Langlands.Representation.Archimedean.RealLeviSlices
import Langlands.Representation.Archimedean.RealSwapFLanding
import Langlands.Representation.Archimedean.RealTemperedCommutantReduction
import Langlands.Representation.Archimedean.RealCharacterPairReducible
import Langlands.Representation.Archimedean.RealLeviModes
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealTemperedTwist
import Langlands.Representation.Archimedean.RealStandardNontrivialProof

/-!
# Invariant form data for tied real standard modules

Proof of `Langlands.Archimedean.RealTemperedFormStatement`. Let `ds` be a list of real blocks whose
real exponents all equal `r`. Replace every induction block of nonzero weight `ℓ` and exponent `t` by
the two characters `sgn^{(ℓ+1) mod 2} |·|^{t-ℓ/2}` and `|·|^{t+ℓ/2}`; this gives the list
`es = ds.flatMap repl`. A chain of block Frobenius maps (tail multipliers) gives a Lie-equivariant
map `T : K(es) → K(ds)` with an `O(n)`-equivariant right inverse `S`. The form is
`B(f, h) = ∫_{O(n)} f · conj (S h)`. It is `O(n)`-invariant. It is anisotropic, by Parseval along the
blocks, because `T` multiplies the iterated block Fourier coefficients by natural numbers. It
satisfies the Lie identity with the scalar `-c_X`, where `c_X` is the derivative at `1` of
`|det|^{-2r}` along `X`: the position characters of `ds` and `es` are dual up to `|·|^{-2r}`, and
the kernel of `T` is orthogonal to `K(ds)`.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct Matrix Manifold ContDiff ComplexConjugate Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTemperedForm

open Langlands.LocalFactor.Archimedean
open RealBlockRotation RealInducedBlockBound RealInducedTorusCore RealLeviModes
open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK_tf (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

attribute [local instance] RealBlockLimit.secondCountableTopology_unitaryCompact

/-! ## Iterated block Fourier coefficients -/

section Coefficients

variable {N : ℕ}

theorem coeffs_const_mul (c : ℂ) (F : Langlands.GeneralLinear N ℝ → ℂ) :
    ∀ L : List (Slot N), coeffs L (fun y => c * F y) = fun g => c * coeffs L F g
  | [] => rfl
  | s :: L => by
    funext g
    simp only [coeffs]
    rw [coeffs_const_mul c F L]
    unfold blockFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only
    ring

/-- If `G = c F` on `O(N)`, the iterated coefficients satisfy the same relation on `O(N)`. -/
theorem coeffs_eq_mul_of_eqOn {F G : Langlands.GeneralLinear N ℝ → ℂ} {c : ℂ}
    (h : ∀ k ∈ unitaryCompact ℝ N, G k = c * F k) (L : List (Slot N))
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    coeffs L G k = c * coeffs L F k := by
  rw [coeffs_congr_of_eqOn (F' := fun y => c * F y) h L k hk, coeffs_const_mul]

/-- If `G = c F` on `O(N)`, the block coefficients satisfy the same relation on `O(N)`. -/
theorem blockFourierCoefficient_eq_mul_of_eqOn {F G : Langlands.GeneralLinear N ℝ → ℂ} {c : ℂ}
    (h : ∀ k ∈ unitaryCompact ℝ N, G k = c * F k) (p : ℕ) (j : ℤ)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N p j G k = c * blockFourierCoefficient N p j F k := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [h _ (mul_mem (blockRotation_mem_unitaryCompact N p θ) hk)]
  ring

/-- A multiplier relation along the block `p` passes through iterated coefficients along
blocks disjoint from `p`. -/
theorem blockFourierCoefficient_coeffs_eq_mul {F G : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F) (hG : Continuous G) {p : ℕ} {j : ℤ} {c : ℂ}
    (h : ∀ k ∈ unitaryCompact ℝ N,
      blockFourierCoefficient N p j G k = c * blockFourierCoefficient N p j F k)
    (L : List (Slot N)) (hd : ∀ t ∈ L, p + 1 < t.p ∨ t.p + 1 < p)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N p j (coeffs L G) k =
      c * blockFourierCoefficient N p j (coeffs L F) k := by
  rw [blockFourierCoefficient_coeffs j hG L hd, blockFourierCoefficient_coeffs j hF L hd]
  exact coeffs_eq_mul_of_eqOn h L hk

/-- Iterated coefficients of `conj F` with the negated modes. -/
theorem coeffs_withModes_conj (F : Langlands.GeneralLinear N ℝ → ℂ) :
    ∀ (L : List (Slot N)) (J : List ℤ),
      coeffs (withModes L (J.map Neg.neg)) (fun y => conj (F y)) =
        fun g => conj (coeffs (withModes L J) F g)
  | [], J => by
    cases J <;> rfl
  | s :: L, [] => rfl
  | s :: L, j :: J => by
    funext g
    simp only [List.map_cons, withModes, coeffs]
    rw [coeffs_withModes_conj F L J, RealSwapFLanding.blockFourierCoefficient_conj]
    simp [setMode]

/-- **Parseval along several blocks, pointwise.** -/
theorem coeffs_zeroModes_mul_conj_eq_sum (D : ℕ) {L : List (Slot N)}
    (hL : L.Pairwise Slot.Disjoint) {u v : Langlands.GeneralLinear N ℝ → ℂ}
    (hu : Continuous u) (huK : IsKFin u) (hdeg : HasDegree L D u) (hv : Continuous v)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    coeffs (zeroModes L) (fun y => u y * conj (v y)) k =
      (2 * (Real.pi : ℂ))⁻¹ ^ L.length * ∑ J ∈ modeLists D L.length,
        coeffs (withModes L J) u k * conj (coeffs (withModes L J) v k) := by
  have e1 := coeffs_mul_right (fun y => u y * conj (v y)) k (zeroModes L) 1
  rw [one_mul] at e1
  have hv' : Continuous fun y => conj (v y) := Complex.continuous_conj.comp hv
  rw [e1, coeffs_zeroModes_mul_eq_sum D L hL hu huK hdeg hv' k hk k]
  simp_rw [coeffs_withModes_conj v L]

/-- The integral over `O(N)` is `(2π)^{-r}` times the integral of the zero-mode
coefficient. -/
theorem integral_eq_inv_mul_coeffs_zeroModes {G : Langlands.GeneralLinear N ℝ → ℂ}
    (hG : Continuous G) (L : List (Slot N)) :
    ∫ k : unitaryCompact ℝ N, G k ∂haarK N =
      (2 * (Real.pi : ℂ))⁻¹ ^ L.length *
        ∫ k : unitaryCompact ℝ N, coeffs (zeroModes L) G k ∂haarK N := by
  rw [integral_coeffs_zeroModes hG L]
  have h2 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h2, one_pow, one_mul]

/-- A continuous nonnegative function with zero integral over `O(N)` vanishes on `O(N)`. -/
theorem eq_zero_of_integral_eq_zero_of_nonneg {Q : Langlands.GeneralLinear N ℝ → ℝ}
    (hQ : Continuous Q) (hnn : ∀ k, 0 ≤ Q k)
    (h : ∫ k : unitaryCompact ℝ N, Q k ∂haarK N = 0) :
    ∀ k ∈ unitaryCompact ℝ N, Q k = 0 := by
  have hcont : Continuous fun k : unitaryCompact ℝ N => Q k := hQ.comp continuous_subtype_val
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => hnn _)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp h
  have heq := (Continuous.ae_eq_iff_eq (haarK N) hcont continuous_const).mp hae
  intro k hk
  exact congrFun heq ⟨k, hk⟩

end Coefficients

/-! ## Conjugation and right derivatives on `GL_n(ℝ)` -/

section Calculus

variable {n : ℕ}

theorem unitsExtension_conj (A : Langlands.GeneralLinear n ℝ → ℂ) :
    unitsExtension (fun g => conj (A g)) = fun y => conj (unitsExtension A y) := by
  funext y
  unfold unitsExtension
  split_ifs <;> simp

theorem contMDiff_conj {A : Langlands.GeneralLinear n ℝ → ℂ}
    (hA : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ A) :
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun g => conj (A g)) := by
  refine contMDiff_of_contDiffOn (ψ := fun y => Complex.conjCLE (unitsExtension A y))
    (Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_unitsExtension hA)) fun g => ?_
  rw [unitsExtension_val, Complex.conjCLE_apply]

/-- Right derivatives along real matrices commute with complex conjugation. -/
theorem rightDerivative_conj {A : Langlands.GeneralLinear n ℝ → ℂ}
    (hA : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ A)
    (X : Matrix (Fin n) (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (fun g => conj (A g)) g =
      conj (rightDerivative (matrixModel ℝ n) X A g) := by
  rw [rightDerivative_eq_fderiv (contMDiff_conj hA), rightDerivative_eq_fderiv hA,
    unitsExtension_conj]
  change fderiv ℝ (fun y => star (unitsExtension A y)) _ _ = star _
  rw [fderiv_star]
  rfl

end Calculus

/-! ## The dual partner and the Lie identity -/

section Partner

variable {n : ℕ}

open RealLinkedJacquetStages RealTemperedTwist

/-- `|det(diag a)|^s conj(δ_{χ'}(a)) = δ_{χ''}(a)` for `χ''_i(x) = conj(χ'_i(x)) |x|^s`. -/
theorem detPow_mul_conj_principalSeriesCharacter (χ' : ℕ → ℝˣ → ℂ) (s : ℂ) (a : Fin n → ℝˣ) :
    detPow n s (Langlands.GeneralLinear.Iwasawa.diagonalUnits a) *
        conj (principalSeriesCharacter ℝ n χ' a) =
      principalSeriesCharacter ℝ n
        (fun i x => conj (χ' i x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) a := by
  rw [detPow_diagonalUnits]
  unfold principalSeriesCharacter
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ht : 0 ≤ ‖((a i : ℝˣ) : ℝ)‖ ^ Module.finrank ℝ ℝ := by positivity
  have hw : ((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) =
      (((((n : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hw, ← Complex.ofReal_cpow ht, map_mul, Complex.conj_ofReal]
  ring

/-- **The dual partner.** If `χ_i(x) conj(χ'_i(x)) |x|^s = 1` on the positions `i < n`, then
`g ↦ |det g|^s conj(v(g))` lies in the principal series of `χ⁻¹` for `v` in that of `χ'`. -/
theorem partner_mem {χ χ' : ℕ → ℝˣ → ℂ} {s : ℂ}
    (hχ : ∀ i : Fin n, ∀ x : ℝˣ, χ i x * (conj (χ' i x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) = 1)
    {v : Langlands.GeneralLinear n ℝ → ℂ} (hv : v ∈ principalSeries ℝ n χ') :
    (fun g => detPow n s g * conj (v g)) ∈ principalSeries ℝ n (fun i x => (χ i x)⁻¹) := by
  rw [mem_principalSeries_iff] at hv ⊢
  refine ⟨RealPrincipalSeriesDuality.contMDiff_mul_fun (contMDiff_detPow s) (contMDiff_conj hv.1), fun a u g => ?_⟩
  have hc : principalSeriesCharacter ℝ n (fun i x => (χ i x)⁻¹) a =
      principalSeriesCharacter ℝ n
        (fun i x => conj (χ' i x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) a := by
    unfold principalSeriesCharacter
    refine Finset.prod_congr rfl fun i _ => ?_
    beta_reduce
    rw [inv_eq_of_mul_eq_one_right (hχ i (a i))]
  rw [hc, ← detPow_mul_conj_principalSeriesCharacter χ' s a, hv.2 a u g, detPow_mul,
    detPow_mul, detPow_of_mem_upperUnipotent s u.2, map_mul]
  ring

theorem continuous_compK {F : Langlands.GeneralLinear n ℝ → ℂ} (hF : Continuous F) :
    Continuous fun k : unitaryCompact ℝ n => F k :=
  hF.comp continuous_subtype_val

theorem integrable_mul_conjK {F G : Langlands.GeneralLinear n ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) :
    Integrable (fun k : unitaryCompact ℝ n => F k * conj (G k)) (haarK n) :=
  RealLeviModes.integrable_of_continuous (G := fun g => F g * conj (G g))
    (hF.mul (Complex.continuous_conj.comp hG))

/-- **Infinitesimal invariance of the conjugate pairing up to a scalar.** For `f` in the
principal series of `χ`, `v` in that of `χ'` and `χ_i conj(χ'_i) |·|^s = 1` (`i < n`),
`∫ (R_X f) conj v + ∫ f conj (R_X v) = -c ∫ f conj v` over `O(n)`, where `c` is the derivative
at `1` of `|det|^s` along `X`. -/
theorem integral_lie_conj {χ χ' : ℕ → ℝˣ → ℂ} {s : ℂ}
    (hχ : ∀ i : Fin n, ∀ x : ℝˣ, χ i x * (conj (χ' i x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) = 1)
    (hχ0 : ∀ i x, χ i x ≠ 0) {f v : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ n χ) (hv : v ∈ principalSeries ℝ n χ')
    (X : Matrix (Fin n) (Fin n) ℝ)
    (hRf : Continuous (rightDerivative (matrixModel ℝ n) X f))
    (hRv : Continuous (rightDerivative (matrixModel ℝ n) X v)) :
    (∫ k : unitaryCompact ℝ n, rightDerivative (matrixModel ℝ n) X f k * conj (v k) ∂haarK n) +
        ∫ k : unitaryCompact ℝ n, f k * conj (rightDerivative (matrixModel ℝ n) X v k) ∂haarK n =
      -(rightDerivative (matrixModel ℝ n) X (detPow n s) 1) *
        ∫ k : unitaryCompact ℝ n, f k * conj (v k) ∂haarK n := by
  have hw := partner_mem hχ hv
  have hfs : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f := hf.1
  have hvs : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ v := hv.1
  have hws : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun g => detPow n s g * conj (v g)) := hw.1
  have h0 : ∫ k : unitaryCompact ℝ n, rightDerivative (matrixModel ℝ n) X
      (fun g => f g * (detPow n s g * conj (v g))) k ∂haarK n = 0 :=
    integral_rightDerivative_eq_zero (RealPrincipalSeriesDuality.contMDiff_mul_fun hfs hws)
      (isModulusEquivariant_mul (fun i x => mul_inv_cancel₀ (hχ0 i x)) hf hw) X
  set c := rightDerivative (matrixModel ℝ n) X (detPow n s) 1 with hc
  have hpt : (fun k : unitaryCompact ℝ n => rightDerivative (matrixModel ℝ n) X
      (fun g => f g * (detPow n s g * conj (v g))) k) = fun k : unitaryCompact ℝ n =>
        rightDerivative (matrixModel ℝ n) X f k * conj (v k) + c * (f k * conj (v k)) +
          f k * conj (rightDerivative (matrixModel ℝ n) X v k) := by
    funext k
    rw [rightDerivative_mul_fun hfs hws, rightDerivative_mul_fun (contMDiff_detPow s)
      (contMDiff_conj hvs), rightDerivative_conj hvs, rightDerivative_detPow,
      detPow_of_mem_unitaryCompact s k.2]
    ring
  have hv' := hvs.continuous
  have hf' := hfs.continuous
  have hA := integrable_mul_conjK hRf hv'
  have hB := (integrable_mul_conjK hf' hv').const_mul c
  have hC := integrable_mul_conjK hf' hRv
  rw [hpt, integral_add (f := fun k : unitaryCompact ℝ n =>
      rightDerivative (matrixModel ℝ n) X f k * conj (v k) + c * (f k * conj (v k)))
      (hA.add hB) hC, integral_add hA hB, integral_const_mul] at h0
  linear_combination h0

end Partner

/-! ## Replacing induction blocks by pairs of characters -/

section Lists

open RealJacquetFrobenius RealBlockPosition

/-- The first character `sgn^{(m+1) mod 2} |·|^{t - m/2}` replacing an induction block of
weight `m` and exponent `t`. -/
def cLow (d : ComplexCharacterData) : RealCharacterData :=
  charData ⟨(d.weight.natAbs + 1) % 2, Nat.mod_lt _ two_pos⟩
    (d.exponent - (d.weight.natAbs : ℂ) / 2)

/-- The second character `|·|^{t + m/2}` replacing an induction block. -/
def cHigh (d : ComplexCharacterData) : RealCharacterData :=
  charData 0 (d.exponent + (d.weight.natAbs : ℂ) / 2)

/-- An induction block of nonzero weight becomes the two characters `cLow, cHigh`; every other
block is kept. -/
def repl : RealBlock → List RealBlock
  | .character c => [.character c]
  | .induced d => if d.weight = 0 then [.induced d] else
      [.character (cLow d), .character (cHigh d)]

theorem realRank_repl (x : RealBlock) : realRank (repl x) = x.rank := by
  cases x with
  | character c => rfl
  | induced d =>
    simp only [repl]
    split_ifs <;> rfl

theorem realRank_flatMap_repl : ∀ ds : List RealBlock, realRank (ds.flatMap repl) = realRank ds
  | [] => rfl
  | x :: ds => by
    have h1 := realRank_repl x
    have h2 := realRank_flatMap_repl ds
    simp only [realRank] at h1 h2 ⊢
    simp [List.flatMap_cons, List.map_append, List.sum_append, h1, h2]

/-- `charFun e t x · conj(charFun e t' x) · |x|^{-2r} = 1` if `t + conj t' = 2r`. -/
theorem charFun_mul_conj (e : Fin 2) {t t' : ℂ} {r : ℝ} (h : t + conj t' = 2 * r) {x : ℝ}
    (hx : x ≠ 0) :
    charFun e t x * (conj (charFun e t' x) * ((|x| : ℝ) : ℂ) ^ (-(2 * r : ℂ))) = 1 := by
  have ha : 0 < |x| := abs_pos.mpr hx
  have h0 : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have harg : (((|x| : ℝ)) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]
    exact Real.pi_pos.ne
  have hc : conj (((|x| : ℝ) : ℂ) ^ t') = ((|x| : ℝ) : ℂ) ^ (conj t') := by
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  have hs : (((x / |x| : ℝ)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, div_pow, sq_abs, div_self (pow_ne_zero 2 hx), Complex.ofReal_one]
  have hp : ((|x| : ℝ) : ℂ) ^ t * ((|x| : ℝ) : ℂ) ^ (conj t') *
      ((|x| : ℝ) : ℂ) ^ (-(2 * r : ℂ)) = 1 := by
    rw [← Complex.cpow_add _ _ h0, ← Complex.cpow_add _ _ h0, h, add_neg_cancel,
      Complex.cpow_zero]
  unfold RealJacquetFrobenius.charFun
  rw [map_mul, map_pow, Complex.conj_ofReal, hc]
  calc _ = ((((x / |x| : ℝ)) : ℂ) ^ 2) ^ e.val * (((|x| : ℝ) : ℂ) ^ t *
        ((|x| : ℝ) : ℂ) ^ (conj t') * ((|x| : ℝ) : ℂ) ^ (-(2 * r : ℂ))) := by ring
    _ = 1 := by rw [hs, hp, one_pow, one_mul]

theorem realPositionCharacter_ne_zero' (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    realPositionCharacter ds i x ≠ 0 := by
  rw [realPositionCharacter_eq_charFun]
  refine left_ne_zero_of_mul_eq_one (charFun_mul_conj (r := 0) _
    (t' := -conj (GramFormula.realPositionExponent ds i)) ?_ x.ne_zero)
  simp

/-- The positions of `ds` and of `ds.flatMap repl` have the same signs, and their exponents
satisfy `t_i + conj t'_i = 2r` when all real exponents of `ds` equal `r`. -/
theorem position_rel (r : ℝ) : ∀ (ds : List RealBlock), (∀ x ∈ ds, realBlockExponent x = r) →
    ∀ i : ℕ, i < realRank ds →
      realPositionSign (ds.flatMap repl) i = realPositionSign ds i ∧
        GramFormula.realPositionExponent ds i +
          conj (GramFormula.realPositionExponent (ds.flatMap repl) i) = 2 * r
  | [], _, i, hi => by simp [realRank] at hi
  | .character c :: ds, h, 0, _ => by
    have hc := h _ List.mem_cons_self
    simp only [realBlockExponent] at hc
    simp only [List.flatMap_cons, repl, List.singleton_append, realPositionSign,
      GramFormula.realPositionExponent, true_and]
    rw [Complex.add_conj, hc]
    push_cast
    ring
  | .character c :: ds, h, i + 1, hi => by
    have ih := position_rel r ds (fun x hx => h x (List.mem_cons_of_mem _ hx)) i (by
      simp only [realRank, List.map_cons, List.sum_cons, RealBlock.rank] at hi ⊢
      omega)
    simpa only [List.flatMap_cons, repl, List.singleton_append, realPositionSign,
      GramFormula.realPositionExponent] using ih
  | .induced d :: ds, h, i, hi => by
    have hd := h _ List.mem_cons_self
    simp only [realBlockExponent] at hd
    have key : d.exponent + conj d.exponent = 2 * r := by
      rw [Complex.add_conj, hd]
      push_cast
      ring
    have hi' : i < 2 + realRank ds := by
      simp only [realRank, List.map_cons, List.sum_cons, RealBlock.rank] at hi ⊢
      omega
    have ih := fun j (hj : j < realRank ds) =>
      position_rel r ds (fun x hx => h x (List.mem_cons_of_mem _ hx)) j hj
    by_cases hw : d.weight = 0
    · obtain _ | _ | j := i
      · simp only [List.flatMap_cons, repl, hw, ite_true, List.singleton_append,
          realPositionSign, GramFormula.realPositionExponent, true_and]
        simp only [map_add, map_div₀, map_natCast, map_ofNat]
        linear_combination key
      · simp only [List.flatMap_cons, repl, hw, ite_true, List.singleton_append,
          realPositionSign, GramFormula.realPositionExponent, true_and]
        simp only [map_sub, map_div₀, map_natCast, map_ofNat]
        linear_combination key
      · simpa only [List.flatMap_cons, repl, hw, ite_true, List.singleton_append,
          realPositionSign, GramFormula.realPositionExponent] using ih j (by omega)
    · obtain _ | _ | j := i
      · simp only [List.flatMap_cons, repl, hw, ite_false, List.cons_append, List.nil_append,
          realPositionSign, GramFormula.realPositionExponent, cLow, charData]
        refine ⟨trivial, ?_⟩
        simp only [map_sub, map_div₀, map_natCast, map_ofNat]
        linear_combination key
      · simp only [List.flatMap_cons, repl, hw, ite_false, List.cons_append, List.nil_append,
          realPositionSign, GramFormula.realPositionExponent, cHigh, charData]
        refine ⟨trivial, ?_⟩
        simp only [map_add, map_div₀, map_natCast, map_ofNat]
        linear_combination key
      · simpa only [List.flatMap_cons, repl, hw, ite_false, List.cons_append, List.nil_append,
          realPositionSign, GramFormula.realPositionExponent] using ih j (by omega)

/-- The position characters of `ds` and of `ds.flatMap repl` are dual: their product with
`|x|^{-2r}` after conjugating the second is `1` on every position inside the rank. -/
theorem position_char (r : ℝ) (ds : List RealBlock) (h : ∀ x ∈ ds, realBlockExponent x = r)
    (i : ℕ) (hi : i < realRank ds) (x : ℝˣ) :
    realPositionCharacter ds i x * (conj (realPositionCharacter (ds.flatMap repl) i x) *
      ((|(x : ℝ)| : ℝ) : ℂ) ^ (-(2 * r : ℂ))) = 1 := by
  obtain ⟨hs, he⟩ := position_rel r ds h i hi
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun, hs]
  exact charFun_mul_conj _ he x.ne_zero

end Lists

/-! ## Chains of block Frobenius maps -/

section Chain

open RealBlockFrobeniusMap RealBlockMultiplier RealCharacterPairReducible RealBlockPosition
open RealBlockJacquet RealTemperedCommutantReduction RealJacquetFrobenius

variable {n : ℕ}

/-- The value `C(⌊|j|/2⌋ + ⌊(ℓ - 1 + ε)/2⌋, ℓ)` of the tail multiplier with sign `1`. -/
def tailNat (ℓ : ℕ) (ε j : ℤ) : ℕ :=
  (j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2).choose ℓ

theorem tailMultiplier_one_eq (ℓ : ℕ) (ε j : ℤ) :
    tailMultiplier ℓ ε 1 j = (tailNat ℓ ε j : ℂ) := by
  unfold tailMultiplier RealBlockMultiplier.extend tailSeq tailNat
  split_ifs <;> simp

/-- Chain data from the standard module of `Z` to that of `X`: a Lie-equivariant linear map
`T` with an `O(n)`-equivariant right inverse `S`, and pairwise disjoint slots at positions
`≥ b` along which `T` multiplies the iterated coefficients on `O(n)` by natural numbers. -/
def ChainData (n b : ℕ) (Z X : List RealBlock) : Prop :=
  ∃ (T : KF n Z →ₗ[ℂ] KF n X) (S : KF n X →ₗ[ℂ] KF n Z) (L : List (Slot n))
    (W : List ℤ → ℕ),
    (∀ f, T (S f) = f) ∧
    (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n X),
      S (realStandardRep n X k f) = realStandardRep n Z k (S f)) ∧
    (∀ (Y : Matrix (Fin n) (Fin n) ℝ) (u : KF n Z),
      T (realStandardLie n Z (1 ⊗ₜ Y) u) = realStandardLie n X (1 ⊗ₜ Y) (T u)) ∧
    L.Pairwise Slot.Disjoint ∧ (∀ t ∈ L, b ≤ t.p) ∧
    ∀ (J : List ℤ), J.length = L.length → ∀ (u : KF n Z) (k : Langlands.GeneralLinear n ℝ),
      k ∈ unitaryCompact ℝ n →
        coeffs (withModes L J) ((T u : KF n X) : Langlands.GeneralLinear n ℝ → ℂ) k =
          (W J : ℂ) * coeffs (withModes L J) (u : Langlands.GeneralLinear n ℝ → ℂ) k

theorem chainData_refl (b : ℕ) (X : List RealBlock) : ChainData n b X X := by
  refine ⟨LinearMap.id, LinearMap.id, [], fun _ => 1, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, List.Pairwise.nil, fun t ht => by simp at ht, fun J hJ u k _ => ?_⟩
  rw [List.length_nil, List.length_eq_zero_iff] at hJ
  subst hJ
  simp [withModes, coeffs]

theorem ChainData.mono {b b' : ℕ} {Z X : List RealBlock} (h : ChainData n b' Z X)
    (hb : b ≤ b') : ChainData n b Z X := by
  obtain ⟨T, S, L, W, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨T, S, L, W, h1, h2, h3, h4, fun t ht => hb.trans (h5 t ht), h6⟩

/-- A slot at the block `p` (only `p` and the mode matter here). -/
def slotAt (p : ℕ) (hp : p + 1 < n) : Slot n := ⟨p, hp, 0, 0, 0, 0, 0, 0⟩

/-- The weights `m j · W J` on the mode lists `j :: J`. -/
def consW (m : ℤ → ℕ) (W : List ℤ → ℕ) : List ℤ → ℕ
  | [] => 1
  | j :: J => m j * W J

/-- **Extending a chain by one block Frobenius map** in front. -/
theorem ChainData.step {b p : ℕ} {Z Y X : List RealBlock} (h : ChainData n b Y X)
    (hpb : p + 1 < b) {ε : ℤ} {σ σ' : ℂ} {μ μ' : ℤ → ℂ}
    (hT : IsBlockFrobData n Z Y p ε σ μ) (hS : IsBlockFrobData n Y Z p ε σ' μ')
    (hrec : IsRecurrent (GramFormula.realPositionExponent Z p -
      GramFormula.realPositionExponent Z (p + 1) + 1) ε μ)
    (m : ℤ → ℕ) (hm : ∀ j, μ j = (m j : ℂ))
    (hid : ∀ f : KF n Y, blockFrobMap hT (blockFrobMap hS f) = f) :
    ChainData n p Z X := by
  obtain ⟨T, S, L, W, hTS, hSK, hTL, hL, hLb, hW⟩ := h
  refine ⟨T ∘ₗ blockFrobMap hT, blockFrobMap hS ∘ₗ S, slotAt p hT.lt :: L, consW m W,
    fun f => ?_, fun k f => ?_, fun Y' u => ?_, ?_, ?_, ?_⟩
  · simp only [LinearMap.comp_apply, hid, hTS]
  · simp only [LinearMap.comp_apply, hSK, blockFrobMap_rightTranslation]
  · simp only [LinearMap.comp_apply, blockFrobMap_rightDerivative hT hrec, hTL]
  · refine List.Pairwise.cons (fun t ht => ?_) hL
    exact Or.inl (lt_of_lt_of_le hpb (hLb t ht))
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact le_rfl
    · exact le_trans (by omega) (hLb t ht)
  · intro J hJ u k hk
    cases J with
    | nil => simp at hJ
    | cons j J =>
      simp only [List.length_cons, add_left_inj] at hJ
      have hd : ∀ t ∈ withModes L J, p + 1 < t.p ∨ t.p + 1 < p := by
        intro t ht
        obtain ⟨s, hs, j', rfl⟩ := mem_withModes ht
        exact Or.inl (lt_of_lt_of_le hpb (hLb s hs))
      simp only [withModes, coeffs, setMode, slotAt, LinearMap.comp_apply, consW]
      rw [blockFourierCoefficient_eq_mul_of_eqOn (fun k' hk' => hW J hJ _ k' hk') p j hk,
        blockFourierCoefficient_coeffs_eq_mul (continuous_coe u) (continuous_coe (blockFrobMap hT u))
          (fun k' hk' => blockFourierCoefficient_blockFrobMap hT u hk' j) _ hd hk, hm]
      push_cast
      ring

section Data

variable (pre post : List RealBlock) {d : ComplexCharacterData}

/-- The parity class `(ℓ + 1) mod 2` for an induction block of weight `ℓ`. -/
def epsW (d : ComplexCharacterData) : ℤ := (((d.weight.natAbs + 1) % 2 : ℕ) : ℤ)

theorem epsW_cases (d : ComplexCharacterData) : epsW d = 0 ∨ epsW d = 1 := by
  unfold epsW
  omega

theorem epsW_par (d : ComplexCharacterData) :
    Even ((d.weight.natAbs : ℤ) - 1 - epsW d) := by
  unfold epsW
  rw [Int.even_iff]
  omega

/-- The two characters replacing an induction block. -/
abbrev pairL (d : ComplexCharacterData) : List RealBlock :=
  [RealBlock.character (cLow d), RealBlock.character (cHigh d)]

/-- The induction block. -/
abbrev indL (d : ComplexCharacterData) : List RealBlock := [RealBlock.induced d]

theorem realRank_pairL (d : ComplexCharacterData) : realRank (pairL d) = 2 := rfl
theorem realRank_indL (d : ComplexCharacterData) : realRank (indL d) = 2 := rfl

/-- The tail multiplier from the two characters to the induction block. -/
theorem dataT (hw : d.weight ≠ 0) (hn : realRank (pre ++ indL d ++ post) = n) :
    IsBlockFrobData n (pre ++ pairL d ++ post) (pre ++ indL d ++ post) (realRank pre) (epsW d) 1
      (tailMultiplier d.weight.natAbs (epsW d) 1) := by
  have hℓ : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hw
  refine IsBlockFrobData.of_mid hn rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hℓ (epsW_cases d) (epsW_par d) (one_pow 2)) ?_ ?_ ?_
  · simp [GramFormula.realPositionExponent, cHigh, charData]
  · simp [GramFormula.realPositionExponent, cLow, charData]
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one]
    simp [realPositionSign, cLow, cHigh, charData, epsW]
    rw [Int.abs_eq_natAbs]
    norm_cast
  · rw [realPositionCharacter_neg_one]
    simp [realPositionSign, cLow, charData]
  · rw [realPositionCharacter_neg_one]
    simp [realPositionSign, cHigh, charData]
  · intro d' hd' j hj hjl
    simp only [realInducedBlockAt, Option.some.injEq] at hd'
    subst hd'
    by_contra hne
    have := (tailMultiplier_ne_zero_iff hℓ (epsW_cases d) (epsW_par d) (one_pow 2) hj).mp hne
    rw [Int.abs_eq_natAbs d.weight] at hjl
    exact lt_asymm hjl this

/-- The inverse tail multiplier from the induction block to the two characters. -/
theorem dataS (hw : d.weight ≠ 0) (hn : realRank (pre ++ indL d ++ post) = n) :
    IsBlockFrobData n (pre ++ indL d ++ post) (pre ++ pairL d ++ post) (realRank pre) (epsW d)
      1⁻¹ (fun k => (tailMultiplier d.weight.natAbs (epsW d) 1 k)⁻¹) := by
  have hℓ : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hw
  have hn' : realRank (pre ++ pairL d ++ post) = n := by
    rw [← hn]
    exact realRank_mid_eq pre post rfl
  refine IsBlockFrobData.of_mid hn' rfl rfl ?_ ?_ ?_
    (isSymmetric_tailMultiplier hℓ (epsW_cases d) (epsW_par d) (one_pow 2)).inv ?_ ?_ ?_
  · simp [GramFormula.realPositionExponent, cLow, charData]
  · simp [GramFormula.realPositionExponent, cHigh, charData]
  · rw [realPositionCharacter_neg_one, realPositionCharacter_neg_one]
    simp [realPositionSign, epsW]
    rw [Int.abs_eq_natAbs]
    norm_cast
  · rw [realPositionCharacter_neg_one]
    simp [realPositionSign, cLow, charData]
  · rw [realPositionCharacter_neg_one]
    simp [realPositionSign, cHigh, charData]
  · intro e he
    simp [realInducedBlockAt] at he

/-- One step of the chain at an induction block of nonzero weight. -/
theorem step_induced (hw : d.weight ≠ 0) (hn : realRank (pre ++ indL d ++ post) = n)
    {X : List RealBlock} (h : ChainData n (realRank pre + 2) (pre ++ indL d ++ post) X) :
    ChainData n (realRank pre) (pre ++ pairL d ++ post) X := by
  have hℓ : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hw
  have hT := dataT pre post hw hn
  have hS := dataS pre post hw hn
  refine h.step (by omega) hT hS ?_ (tailNat d.weight.natAbs (epsW d))
    (tailMultiplier_one_eq _ _) ?_
  · have he : GramFormula.realPositionExponent (pre ++ pairL d ++ post) (realRank pre) -
        GramFormula.realPositionExponent (pre ++ pairL d ++ post) (realRank pre + 1) + 1 =
          1 - (d.weight.natAbs : ℂ) := by
      rw [exponent_mid_zero pre post (realRank_pairL d ▸ two_pos),
        exponent_mid_one pre post (realRank_pairL d ▸ one_lt_two)]
      simp only [GramFormula.realPositionExponent, cLow, cHigh, charData]
      ring
    rw [he]
    exact isRecurrent_tailMultiplier hℓ (epsW_cases d) (epsW_par d) (one_pow 2)
  · intro f
    refine blockFrobMap_blockFrobMap_eq hS hT f fun j hj hne k hk => ?_
    have h0 : tailMultiplier d.weight.natAbs (epsW d) 1 j = 0 := by
      by_contra h0
      exact hne (mul_inv_cancel₀ h0)
    have hle : ¬ ((d.weight.natAbs : ℤ) < |j|) := fun hlt =>
      (tailMultiplier_ne_zero_iff hℓ (epsW_cases d) (epsW_par d) (one_pow 2) hj).mpr hlt h0
    have hlt := abs_lt_of_parity (epsW_par d) hj (not_lt.mp hle)
    have hblk : realInducedBlockAt (pre ++ indL d ++ post) (realRank pre) = some d := by
      have := realInducedBlockAt_mid pre (indL d) post (j := 0) (by rw [realRank_indL]; norm_num)
      rwa [add_zero] at this
    exact f.2.1.2 (realRank pre) d hblk j
      (by rw [Int.abs_eq_natAbs d.weight]; exact hlt) k

end Data

/-- **The chain.** From the standard module of `pre ++ rest.flatMap repl` to that of
`pre ++ rest`, with slots at positions `≥ realRank pre`. -/
theorem chain : ∀ (rest pre : List RealBlock), realRank (pre ++ rest) = n →
    ChainData n (realRank pre) (pre ++ rest.flatMap repl) (pre ++ rest)
  | [], pre, _ => by simpa using chainData_refl (n := n) (realRank pre) pre
  | x :: rest, pre, hn => by
    have hn' : realRank ((pre ++ [x]) ++ rest) = n := by simpa using hn
    have ih := chain rest (pre ++ [x]) hn'
    have e2 : pre ++ x :: rest = pre ++ [x] ++ rest := by simp
    by_cases hx : repl x = [x]
    · have e1 : pre ++ (x :: rest).flatMap repl = pre ++ [x] ++ rest.flatMap repl := by
        simp [List.flatMap_cons, hx]
      rw [e1, e2]
      exact ih.mono (by rw [RealLeviSlices.realRank_append]; omega)
    · obtain ⟨d, rfl, hw⟩ : ∃ d, x = RealBlock.induced d ∧ d.weight ≠ 0 := by
        cases x with
        | character c => exact (hx rfl).elim
        | induced d => exact ⟨d, rfl, fun h => hx (by simp [repl, h])⟩
      have e1 : pre ++ (RealBlock.induced d :: rest).flatMap repl =
          pre ++ pairL d ++ rest.flatMap repl := by
        simp [List.flatMap_cons, repl, hw]
      have hnY : realRank (pre ++ indL d ++ rest.flatMap repl) = n := by
        rw [← hn', RealLeviSlices.realRank_append, RealLeviSlices.realRank_append, realRank_flatMap_repl, RealLeviSlices.realRank_append]
        rw [RealLeviSlices.realRank_append]
      have hb : realRank (pre ++ [RealBlock.induced d]) = realRank pre + 2 := by
        rw [RealLeviSlices.realRank_append]
        rfl
      rw [hb] at ih
      rw [e1, e2]
      exact step_induced pre (rest.flatMap repl) hw hnY ih

end Chain

/-! ## The form -/

section Form

open RealTemperedCommutantReduction RealBlockJacquet RealInducedStandardBound RealLinkedJacquetStages

variable {n : ℕ} {ds es : List RealBlock}

theorem integrable_kf (f : KF n ds) (h : KF n es) :
    Integrable (fun k : unitaryCompact ℝ n => (f : Langlands.GeneralLinear n ℝ → ℂ) k *
      conj ((h : Langlands.GeneralLinear n ℝ → ℂ) k)) (haarK n) :=
  integrable_mul_conjK (continuous_coe f) (continuous_coe h)

/-- The form `B(f, h) = ∫_{O(n)} f(k) conj((S h)(k)) dk`. -/
def form (S : KF n ds →ₗ[ℂ] KF n es) : KF n ds →ₗ[ℂ] KF n ds →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f h => ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
      conj (((S h : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n)
    (fun f₁ f₂ h => by
      rw [← integral_add (integrable_kf f₁ (S h)) (integrable_kf f₂ (S h))]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c f h => by
      rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun f h₁ h₂ => by
      rw [map_add, ← integral_add (integrable_kf f (S h₁)) (integrable_kf f (S h₂))]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add])
    (fun c f h => by
      rw [map_smul, smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
      ring)

theorem form_apply (S : KF n ds →ₗ[ℂ] KF n es) (f h : KF n ds) :
    form S f h = ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
      conj (((S h : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n :=
  rfl

/-- `O(n)`-invariance of the form. -/
theorem form_rep (S : KF n ds →ₗ[ℂ] KF n es)
    (hS : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds),
      S (realStandardRep n ds k f) = realStandardRep n es k (S f))
    (k : Matrix.unitaryGroup (Fin n) ℝ) (f h : KF n ds) :
    form S (realStandardRep n ds k f) (realStandardRep n ds k h) = form S f h := by
  rw [form_apply, form_apply, hS]
  exact integral_mul_right_eq_self (μ := haarK n)
    (fun x : unitaryCompact ℝ n => (f : Langlands.GeneralLinear n ℝ → ℂ) x *
      conj (((S h : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) x))
    (⟨Unitary.toUnits k, k.2⟩ : unitaryCompact ℝ n)

section Weights

variable {T : KF n es →ₗ[ℂ] KF n ds} {S : KF n ds →ₗ[ℂ] KF n es} {L : List (Slot n)}
  {W : List ℤ → ℕ}

/-- **The kernel of `T` is orthogonal to the standard module.** -/
theorem integral_mul_conj_eq_zero_of_ker (hTS : ∀ f, T (S f) = f)
    (hL : L.Pairwise Slot.Disjoint)
    (hW : ∀ (J : List ℤ), J.length = L.length → ∀ (u : KF n es) (k : Langlands.GeneralLinear n ℝ),
      k ∈ unitaryCompact ℝ n →
        coeffs (withModes L J) ((T u : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) k =
          (W J : ℂ) * coeffs (withModes L J) (u : Langlands.GeneralLinear n ℝ → ℂ) k)
    (f : KF n ds) {w : KF n es} (hw : T w = 0) :
    ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
      conj ((w : Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n = 0 := by
  obtain ⟨D, hD⟩ := exists_hasDegree (continuous_coe f) f.2.2 L
  have h0 : ∀ k : unitaryCompact ℝ n, coeffs (zeroModes L)
      (fun y => (f : Langlands.GeneralLinear n ℝ → ℂ) y *
        conj ((w : Langlands.GeneralLinear n ℝ → ℂ) y)) k = 0 := by
    intro k
    rw [coeffs_zeroModes_mul_conj_eq_sum D hL (continuous_coe f) f.2.2 hD (continuous_coe w) k.2]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun J hJ => ?_)
    have hJl := (mem_modeLists hJ).1
    have e1 : coeffs (withModes L J) (f : Langlands.GeneralLinear n ℝ → ℂ) k = (W J : ℂ) *
        coeffs (withModes L J) ((S f : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) k := by
      rw [← hW J hJl (S f) k k.2, hTS]
    have e2 : (W J : ℂ) * coeffs (withModes L J) (w : Langlands.GeneralLinear n ℝ → ℂ) k = 0 := by
      rw [← hW J hJl w k k.2, hw]
      exact coeffs_eq_zero_of_eqOn (fun _ _ => rfl) _ _ k.2
    have e3 : (W J : ℂ) * conj (coeffs (withModes L J) (w : Langlands.GeneralLinear n ℝ → ℂ) k) =
        conj ((W J : ℂ) * coeffs (withModes L J) (w : Langlands.GeneralLinear n ℝ → ℂ) k) := by
      rw [map_mul, Complex.conj_natCast]
    rw [e1, mul_comm (W J : ℂ), mul_assoc, e3, e2, map_zero, mul_zero]
  have hc : Continuous fun y => (f : Langlands.GeneralLinear n ℝ → ℂ) y *
      conj ((w : Langlands.GeneralLinear n ℝ → ℂ) y) :=
    (continuous_coe f).mul (Complex.continuous_conj.comp (continuous_coe w))
  refine (integral_eq_inv_mul_coeffs_zeroModes hc L).trans ?_
  simp only [h0, integral_zero, mul_zero]

/-- **Anisotropy.** -/
theorem eq_zero_of_integral_mul_conj (hTS : ∀ f, T (S f) = f)
    (hL : L.Pairwise Slot.Disjoint)
    (hW : ∀ (J : List ℤ), J.length = L.length → ∀ (u : KF n es) (k : Langlands.GeneralLinear n ℝ),
      k ∈ unitaryCompact ℝ n →
        coeffs (withModes L J) ((T u : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) k =
          (W J : ℂ) * coeffs (withModes L J) (u : Langlands.GeneralLinear n ℝ → ℂ) k)
    (f : KF n ds)
    (h0 : ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
      conj (((S f : KF n es) : Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n = 0) :
    f = 0 := by
  obtain ⟨D, hD⟩ := exists_hasDegree (continuous_coe f) f.2.2 L
  set F : Langlands.GeneralLinear n ℝ → ℂ := (f : Langlands.GeneralLinear n ℝ → ℂ) with hF
  set v : Langlands.GeneralLinear n ℝ → ℂ := ((S f : KF n es) : Langlands.GeneralLinear n ℝ → ℂ)
    with hv
  have hFc : Continuous F := continuous_coe f
  have hvc : Continuous v := continuous_coe (S f)
  have hrel : ∀ J ∈ modeLists D L.length, ∀ k ∈ unitaryCompact ℝ n,
      coeffs (withModes L J) F k = (W J : ℂ) * coeffs (withModes L J) v k := by
    intro J hJ k hk
    rw [hF, hv, ← hW J (mem_modeLists hJ).1 (S f) k hk, hTS]
  set c : ℂ := (2 * (Real.pi : ℂ))⁻¹ ^ L.length with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ (inv_ne_zero
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  set Q : Langlands.GeneralLinear n ℝ → ℝ := fun g => ∑ J ∈ modeLists D L.length,
    (W J : ℝ) * ‖coeffs (withModes L J) v g‖ ^ 2 with hQ
  have hQc : Continuous Q :=
    continuous_finsetSum _ fun J _ => continuous_const.mul ((continuous_coeffs hvc _).norm.pow 2)
  have hQnn : ∀ g, 0 ≤ Q g := fun g => Finset.sum_nonneg fun J _ => by positivity
  have hpt : ∀ k : unitaryCompact ℝ n,
      coeffs (zeroModes L) (fun y => F y * conj (v y)) k = c * (Q k : ℂ) := by
    intro k
    rw [coeffs_zeroModes_mul_conj_eq_sum D hL hFc f.2.2 hD hvc k.2, hQ]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [hrel J hJ k k.2, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have e1 : ∫ k : unitaryCompact ℝ n, F k * conj (v k) ∂haarK n =
      c * ∫ k : unitaryCompact ℝ n, c * (Q k : ℂ) ∂haarK n := by
    refine (integral_eq_inv_mul_coeffs_zeroModes (hFc.mul (Complex.continuous_conj.comp hvc))
      L).trans ?_
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_complex_ofReal, h0] at e1
  have hQ0 : ∫ k : unitaryCompact ℝ n, Q k ∂haarK n = 0 := by
    rcases mul_eq_zero.mp e1.symm with h | h
    · exact absurd h hc0
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc0
    exact_mod_cast h
  have hQK := eq_zero_of_integral_eq_zero_of_nonneg hQc hQnn hQ0
  have hcf : ∀ J ∈ modeLists D L.length, ∀ k ∈ unitaryCompact ℝ n,
      coeffs (withModes L J) F k = 0 := by
    intro J hJ k hk
    have hz := hQK k hk
    simp only [hQ] at hz
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => by positivity)).mp hz J hJ
    rw [hrel J hJ k hk]
    rcases mul_eq_zero.mp hz' with h | h
    · rw [show (W J : ℂ) = 0 by exact_mod_cast h, zero_mul]
    · rw [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h), mul_zero]
  have hff : ∀ k : unitaryCompact ℝ n,
      coeffs (zeroModes L) (fun y => F y * conj (F y)) k = 0 := by
    intro k
    rw [coeffs_zeroModes_mul_conj_eq_sum D hL hFc f.2.2 hD hFc k.2]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun J hJ => ?_)
    rw [hcf J hJ k k.2, zero_mul]
  have hint : ∫ k : unitaryCompact ℝ n, F k * conj (F k) ∂haarK n = 0 := by
    have hc : Continuous fun y => F y * conj (F y) := hFc.mul (Complex.continuous_conj.comp hFc)
    refine (integral_eq_inv_mul_coeffs_zeroModes hc L).trans ?_
    simp only [hff, integral_zero, mul_zero]
  have hnorm : ∫ k : unitaryCompact ℝ n, ‖F k‖ ^ 2 ∂haarK n = 0 := by
    have e : ∀ k : unitaryCompact ℝ n, F k * conj (F k) = ((‖F k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e] at hint
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hfK := eq_zero_of_integral_eq_zero_of_nonneg (Q := fun g => ‖F g‖ ^ 2)
    (hFc.norm.pow 2) (fun _ => by positivity) hnorm
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1
    (principalSeries ℝ n _).zero_mem fun k hk => ?_
  have := hfK k hk
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
  simpa [hF] using this

end Weights

/-- **The Lie identity.** -/
theorem form_lie (r : ℝ) (hr : ∀ x ∈ ds, realBlockExponent x = r) (hn : realRank ds = n)
    {T : KF n (ds.flatMap repl) →ₗ[ℂ] KF n ds} {S : KF n ds →ₗ[ℂ] KF n (ds.flatMap repl)}
    {L : List (Slot n)} {W : List ℤ → ℕ} (hTS : ∀ f, T (S f) = f)
    (hTL : ∀ (Y : Matrix (Fin n) (Fin n) ℝ) (u : KF n (ds.flatMap repl)),
      T (realStandardLie n (ds.flatMap repl) (1 ⊗ₜ Y) u) = realStandardLie n ds (1 ⊗ₜ Y) (T u))
    (hL : L.Pairwise Slot.Disjoint)
    (hW : ∀ (J : List ℤ), J.length = L.length →
      ∀ (u : KF n (ds.flatMap repl)) (k : Langlands.GeneralLinear n ℝ),
      k ∈ unitaryCompact ℝ n →
        coeffs (withModes L J) ((T u : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) k =
          (W J : ℂ) * coeffs (withModes L J) (u : Langlands.GeneralLinear n ℝ → ℂ) k)
    (X : Matrix (Fin n) (Fin n) ℝ) (f h : KF n ds) :
    form S (realStandardLie n ds (1 ⊗ₜ X) f) h + form S f (realStandardLie n ds (1 ⊗ₜ X) h) =
      -(rightDerivative (matrixModel ℝ n) X (detPow n (-(2 * r : ℂ))) 1) * form S f h := by
  have hTw : T (S (realStandardLie n ds (1 ⊗ₜ X) h) -
      realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S h)) = 0 := by
    rw [map_sub, hTL, hTS, hTS, sub_self]
  have hχ : ∀ i : Fin n, ∀ x : ℝˣ, realPositionCharacter ds i x *
      (conj (realPositionCharacter (ds.flatMap repl) i x) *
        ((|(x : ℝ)| : ℝ) : ℂ) ^ (-(2 * r : ℂ))) = 1 :=
    fun i x => position_char r ds hr i (by rw [hn]; exact i.2) x
  have hRf : Continuous
      (rightDerivative (matrixModel ℝ n) X (f : Langlands.GeneralLinear n ℝ → ℂ)) := by
    simpa only [realStandardLie_one_tmul_apply_coe] using
      continuous_coe (realStandardLie n ds (1 ⊗ₜ X) f)
  have hRv : Continuous (rightDerivative (matrixModel ℝ n) X
      ((S h : KF n (ds.flatMap repl)) : Langlands.GeneralLinear n ℝ → ℂ)) := by
    simpa only [realStandardLie_one_tmul_apply_coe] using
      continuous_coe (realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S h))
  have key := integral_lie_conj hχ (fun i x => realPositionCharacter_ne_zero' ds i x) f.2.1.1
    (S h).2.1.1 X hRf hRv
  have hz := integral_mul_conj_eq_zero_of_ker hTS hL hW f hTw
  have e : ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
        conj (((S (realStandardLie n ds (1 ⊗ₜ X) h) : KF n (ds.flatMap repl)) :
          Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n =
      (∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
        conj (((realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S h) :
          KF n (ds.flatMap repl)) : Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n) +
      ∫ k : unitaryCompact ℝ n, (f : Langlands.GeneralLinear n ℝ → ℂ) k *
        conj (((S (realStandardLie n ds (1 ⊗ₜ X) h) -
          realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S h) : KF n (ds.flatMap repl)) :
            Langlands.GeneralLinear n ℝ → ℂ) k) ∂haarK n := by
    rw [← integral_add (integrable_kf f _) (integrable_kf f _)]
    congr 1
    funext k
    simp only [Submodule.coe_sub, Pi.sub_apply, map_sub]
    ring
  rw [form_apply, form_apply, form_apply, e, hz, add_zero]
  simp only [realStandardLie_one_tmul_apply_coe]
  exact key

end Form

end RealTemperedForm

open Langlands.LocalFactor.Archimedean RealTemperedForm RealTemperedCommutantReduction in
/-- **Nontriviality and invariant form data for tied real standard modules.** -/
theorem realTemperedForm : RealTemperedFormStatement := by
  intro n ds hn he
  obtain ⟨r, hr⟩ : ∃ r : ℝ, ∀ x ∈ ds, realBlockExponent x = r := by
    cases ds with
    | nil => exact ⟨0, fun x hx => by simp at hx⟩
    | cons y ys => exact ⟨realBlockExponent y, fun x hx => he x hx y List.mem_cons_self⟩
  refine ⟨realStandardNontrivial n ds hn, ?_⟩
  have hch : ChainData n 0 (ds.flatMap repl) ds := by
    have h := chain ds [] (by simpa using hn)
    have h0 : realRank ([] : List RealBlock) = 0 := rfl
    rw [h0] at h
    simpa using h
  obtain ⟨T, S, L, W, hTS, hSK, hTL, hL, -, hW⟩ := hch
  exact ⟨form S, fun f hf => eq_zero_of_integral_mul_conj hTS hL hW f (by rwa [form_apply] at hf),
    form_rep S hSK, fun X => ⟨_, fun f h => form_lie r hr hn hTS hTL hL hW X f h⟩⟩

end Langlands.Archimedean
