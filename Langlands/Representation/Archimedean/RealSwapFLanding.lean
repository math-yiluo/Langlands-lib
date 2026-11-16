import Langlands.Representation.Archimedean.RealBlockTransposition
import Langlands.Representation.Archimedean.RealSwapLandingStatement
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.JacquetKernel
import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# High block modes after two block multipliers on `GL_3(ℝ)`

Let `c` be a real character data, `d` a complex character data of weight `m`, `ℓ = |m|`, and
`μ₀, μ₁` multipliers as in `RealSwapLandingCharacterFirstStatement`. Let `f` be a continuous
right `O(3)`-finite function whose left Fourier modes along `r_0` are smaller than `ℓ` on
`O(3)`, `g₁` obtained from `f` by the multiplier `μ₁` along `r_1` and `g` from `g₁` by `μ₀`
along `r_0`. Assuming the landing statement, `highModes_eq_zero` shows that the modes of `g`
along `r_1` are smaller than `ℓ` on `O(3)`, provided the projection `G` of `g` onto its modes
`≥ ℓ` along `r_1` has the sign equivariance of the principal series of `[c, d]`, possibly
twisted by a power of the sign of the determinant. The proof pairs `g` against test functions
built from the standard module of `[c, d]` and uses the transposition of block multipliers.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSwapFLanding

open RealPrincipalSeriesDuality RealBlockFourierFinite RealBlockJacquet RealBlockTransposition
open RealBlockMultiplier RealBlockRotation RealBlockPropagation RealBlockDerivative
open PrincipalSeriesExtension GramFormula
open Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK'' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {N : ℕ}

/-! ## The sign of the determinant -/

/-- The sign `det x / |det x|` of the determinant of `x ∈ GL_N(ℝ)`, as a complex number. -/
def sgnDet (N : ℕ) (x : Langlands.GeneralLinear N ℝ) : ℂ :=
  (((x : Matrix (Fin N) (Fin N) ℝ).det / |(x : Matrix (Fin N) (Fin N) ℝ).det| : ℝ) : ℂ)

theorem det_ne_zero (x : Langlands.GeneralLinear N ℝ) :
    (x : Matrix (Fin N) (Fin N) ℝ).det ≠ 0 :=
  (Matrix.isUnits_det_units x).ne_zero

theorem continuous_sgnDet : Continuous (sgnDet N) := by
  have h : Continuous fun x : Langlands.GeneralLinear N ℝ =>
      (x : Matrix (Fin N) (Fin N) ℝ).det :=
    continuous_id.matrix_det.comp Units.continuous_val
  exact Complex.continuous_ofReal.comp
    (h.div h.abs fun x => abs_ne_zero.mpr (det_ne_zero x))

theorem sgnDet_mul (x y : Langlands.GeneralLinear N ℝ) :
    sgnDet N (x * y) = sgnDet N x * sgnDet N y := by
  unfold sgnDet
  rw [Units.val_mul, Matrix.det_mul, abs_mul, mul_div_mul_comm, Complex.ofReal_mul]

theorem sgnDet_mul_self (x : Langlands.GeneralLinear N ℝ) : sgnDet N x * sgnDet N x = 1 := by
  unfold sgnDet
  rw [← Complex.ofReal_mul, div_mul_div_comm, ← sq, ← sq, sq_abs,
    div_self (pow_ne_zero 2 (det_ne_zero x)), Complex.ofReal_one]

theorem sgnDet_pow_mul_self (e : ℕ) (x : Langlands.GeneralLinear N ℝ) :
    sgnDet N x ^ e * sgnDet N x ^ e = 1 := by
  rw [← mul_pow, sgnDet_mul_self, one_pow]

theorem conj_sgnDet (x : Langlands.GeneralLinear N ℝ) : conj (sgnDet N x) = sgnDet N x :=
  Complex.conj_ofReal _

theorem sgnDet_blockRotation (p : ℕ) (θ : ℝ) : sgnDet N (blockRotation N p θ) = 1 := by
  rw [show θ = θ / 2 + θ / 2 by ring, blockRotation_add, sgnDet_mul, sgnDet_mul_self]

theorem sgnDet_blockRotation_mul (p : ℕ) (θ : ℝ) (x : Langlands.GeneralLinear N ℝ) :
    sgnDet N (blockRotation N p θ * x) = sgnDet N x := by
  rw [sgnDet_mul, sgnDet_blockRotation, one_mul]

/-! ## Twists, conjugates and block Fourier coefficients -/

/-- `Φ_j (F · sgnDet^e) (g) = sgnDet(g)^e Φ_j F (g)`. -/
theorem blockFourierCoefficient_mul_sgnDet_pow (p : ℕ) (j : ℤ) (e : ℕ)
    (F : Langlands.GeneralLinear N ℝ → ℂ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j (fun x => F x * sgnDet N x ^ e) g =
      sgnDet N g ^ e * blockFourierCoefficient N p j F g := by
  unfold blockFourierCoefficient
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [sgnDet_blockRotation_mul]
  ring

theorem continuous_mul_sgnDet_pow {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (e : ℕ) : Continuous fun x => F x * sgnDet N x ^ e :=
  hF.mul (continuous_sgnDet.pow e)

theorem mem_kFiniteVectors_mul_sgnDet_pow {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) (e : ℕ) :
    (fun x => F x * sgnDet N x ^ e) ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
        (unitaryCompact ℝ N) := by
  rw [mem_kFiniteVectors_iff] at hF ⊢
  let T : (Langlands.GeneralLinear N ℝ → ℂ) →ₗ[ℂ] (Langlands.GeneralLinear N ℝ → ℂ) :=
    { toFun := fun F x => F x * sgnDet N x ^ e
      map_add' := fun F G => funext fun x => add_mul _ _ _
      map_smul' := fun c F => funext fun x => by simp [mul_assoc] }
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) (k : Langlands.GeneralLinear N ℝ)
        (fun x => F x * sgnDet N x ^ e)) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N =>
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
          (k : Langlands.GeneralLinear N ℝ) F)).map T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨sgnDet N k ^ e • Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
      (k : Langlands.GeneralLinear N ℝ) F,
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), ?_⟩
    funext x
    change sgnDet N k ^ e * F (x * k) * sgnDet N x ^ e = F (x * k) * sgnDet N (x * k) ^ e
    rw [sgnDet_mul, mul_pow]
    ring
  exact Submodule.finiteDimensional_of_le hle

/-- `Φ_j (conj F) (g) = conj (Φ_{-j} F (g))`. -/
theorem blockFourierCoefficient_conj (p : ℕ) (j : ℤ) (F : Langlands.GeneralLinear N ℝ → ℂ)
    (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p j (fun x => conj (F x)) g =
      conj (blockFourierCoefficient N p (-j) F g) := by
  unfold blockFourierCoefficient
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- Block Fourier coefficients at points of `O(N)` only depend on the values on `O(N)`. -/
theorem blockFourierCoefficient_congr {F₁ F₂ : Langlands.GeneralLinear N ℝ → ℂ}
    (h : ∀ x ∈ unitaryCompact ℝ N, F₁ x = F₂ x) (p : ℕ) (j : ℤ) {x : Langlands.GeneralLinear N ℝ}
    (hx : x ∈ unitaryCompact ℝ N) :
    blockFourierCoefficient N p j F₁ x = blockFourierCoefficient N p j F₂ x := by
  unfold blockFourierCoefficient
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [h _ (Subgroup.mul_mem _ (blockRotation_mem_unitaryCompact N p θ) hx)]

/-! ## Block multipliers on `O(N)`-finite functions -/

/-- The block Fourier coefficients of a continuous right `O(N)`-finite function are right
`O(N)`-finite. -/
theorem mem_kFiniteVectors_blockFourierCoefficient (p : ℕ) (i : ℤ)
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (hFK : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) :
    blockFourierCoefficient N p i F ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
        (unitaryCompact ℝ N) := by
  rw [mem_kFiniteVectors_iff] at hFK ⊢
  set W := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
      (k : Langlands.GeneralLinear N ℝ) F) with hW
  have hWc : ∀ w ∈ W, Continuous w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact hF.comp (continuous_id.mul continuous_const)
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.const_smul c
  let T : W →ₗ[ℂ] (Langlands.GeneralLinear N ℝ → ℂ) :=
    { toFun := fun w => blockFourierCoefficient N p i (w : Langlands.GeneralLinear N ℝ → ℂ)
      map_add' := fun w w' => funext fun g => by
        simp only [Submodule.coe_add, Pi.add_apply]
        exact blockFourierCoefficient_add p i (hWc _ w.2) (hWc _ w'.2) g
      map_smul' := fun c w => funext fun g => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact blockFourierCoefficient_smul p i c _ g }
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ N =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ) (k : Langlands.GeneralLinear N ℝ)
        (blockFourierCoefficient N p i F)) ≤ LinearMap.range T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨_, Submodule.subset_span ⟨k, rfl⟩⟩, funext fun g => ?_⟩
    exact blockFourierCoefficient_rightTranslation N p i F (k : Langlands.GeneralLinear N ℝ) g
  have : FiniteDimensional ℂ W := hFK
  exact Submodule.finiteDimensional_of_le hle

/-- **Block multipliers.** For a continuous right `O(N)`-finite `F` and any `ν : ℤ → ℂ` there is
a continuous right `O(N)`-finite `F'` with `Φ_j F' = ν_j Φ_j F` on `O(N)` for all `j`. -/
theorem exists_multiplier {p : ℕ} (hp : p + 1 < N) {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : Continuous F)
    (hFK : F ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
      (unitaryCompact ℝ N)) (ν : ℤ → ℂ) :
    ∃ F' : Langlands.GeneralLinear N ℝ → ℂ, Continuous F' ∧
      F' ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ))
        (unitaryCompact ℝ N) ∧
      ∀ j : ℤ, ∀ g ∈ unitaryCompact ℝ N,
        blockFourierCoefficient N p j F' g = ν j * blockFourierCoefficient N p j F g := by
  obtain ⟨D, hD⟩ := exists_bound p hF hFK
  set I : Finset ℤ := Finset.Icc (-(D : ℤ)) D with hI
  set C : ℤ → ℂ := fun i => (2 * (Real.pi : ℂ))⁻¹ * ν i with hC
  refine ⟨fun x => ∑ i ∈ I, C i * blockFourierCoefficient N p i F x, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_blockFourierCoefficient p i hF)
  · have e : (fun x => ∑ i ∈ I, C i * blockFourierCoefficient N p i F x) =
        ∑ i ∈ I, C i • blockFourierCoefficient N p i F := by
      funext x
      simp [Finset.sum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (mem_kFiniteVectors_blockFourierCoefficient p i hF hFK)
  · intro j g hg
    rw [blockFourierCoefficient_eq_coeff N p j]
    have e : (fun θ : ℝ => (fun x => ∑ i ∈ I, C i * blockFourierCoefficient N p i F x)
        (blockRotation N p θ * g)) =
        fun θ => ∑ i ∈ I, (C i * blockFourierCoefficient N p i F g) * expMode i θ := by
      funext θ
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [blockFourierCoefficient_blockRotation_mul hp, expMode]
      ring
    rw [e, coeff_finset_sum_expMode]
    split_ifs with hj
    · rw [hC]
      field_simp
    · have hj' : (D : ℤ) < |j| := by
        rw [hI, Finset.mem_Icc, ← abs_le] at hj
        exact not_le.mp hj
      rw [hD j hj' g hg, mul_zero]

/-! ## Recurrences and symmetries of reflected multipliers -/

theorem isRecurrent_comp_neg {δ : ℂ} {ε : ℤ} {μ : ℤ → ℂ} (h : IsRecurrent δ ε μ) :
    IsRecurrent δ ε (fun k => μ (-k)) := by
  intro k hk
  have hk' : Even (-k - 2 - ε) := by
    have e : -k - 2 - ε = -(k - ε) - 2 * (ε + 1) := by ring
    rw [e]
    exact hk.neg.sub (even_two_mul _)
  have e := h (-k - 2) hk'
  rw [show -k - 2 + 2 = -k by ring] at e
  show μ (-(k + 2)) * (δ + k) = ((k : ℂ) + 2 - δ) * μ (-k)
  rw [show -(k + 2) = -k - 2 by ring]
  push_cast at e
  linear_combination e

theorem isSymmetric_comp_neg {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ} (hσ : σ * σ = 1)
    (h : IsSymmetric ε σ μ) : IsSymmetric ε σ (fun k => μ (-k)) := by
  intro k hk
  show μ (-(-k)) = σ * μ (-k)
  rw [neg_neg, h k hk, ← mul_assoc, hσ, one_mul]

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

/-! ## The standard module of `[c, d]` -/

/-- `χ_i(e^x) = e^{t_i x}` for the position characters and exponents of a list of blocks. -/
theorem realPositionCharacter_exp (ds : List RealBlock) (i : ℕ) (x : ℝ) :
    realPositionCharacter ds i (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
      Complex.exp (realPositionExponent ds i * x) := by
  rw [realPositionCharacter_eq_signUnit_mul]
  have hs : signUnit (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') = 1 := by
    unfold signUnit
    rw [ite_eq_left (by simpa using Real.exp_pos x)]
  rw [hs, RealStrictCharacterLanglandsQuotient.realPositionCharacter_one, one_mul, Units.val_mk0,
    abs_of_pos (Real.exp_pos x), ofReal_exp_cpow, mul_comm ((x : ℝ) : ℂ)]

/-- The only induction block of `[c, d]` starts at position `1` and is `d`. -/
theorem realInducedBlockAt_character_induced (c : RealCharacterData) (d : ComplexCharacterData)
    {p : ℕ} {d' : ComplexCharacterData}
    (h : realInducedBlockAt [RealBlock.character c, RealBlock.induced d] p = some d') :
    p = 1 ∧ d' = d := by
  rcases p with _ | _ | _ | p
  · simp [realInducedBlockAt] at h
  · simp only [realInducedBlockAt, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [realInducedBlockAt] at h
  · simp [realInducedBlockAt] at h

/-- **Membership in the standard module of `[c, d]`.** A function of the principal series of
the position characters of `[c, d]` whose Fourier coefficients of weight `|k| < |m|` along
`r_1` vanish on `O(3)` lies in the standard module of `[c, d]`. -/
theorem mem_realStandardModule_character_induced (c : RealCharacterData)
    (d : ComplexCharacterData) {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ 3
      (realPositionCharacter [RealBlock.character c, RealBlock.induced d]))
    (hK : ∀ k : ℤ, |k| < |d.weight| → ∀ g ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 k f g = 0) :
    f ∈ realStandardModule 3 [RealBlock.character c, RealBlock.induced d] := by
  refine (mem_realStandardModule_iff 3 _ f).mpr ⟨hf, fun p d' hd k hk g => ?_⟩
  obtain ⟨hp, hd'⟩ := realInducedBlockAt_character_induced c d hd
  subst hp
  rw [hd'] at hk
  have h : 1 + 1 < 3 := by norm_num
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  by_cases hpar : (-1 : ℂ) ^ k =
      realPositionCharacter [RealBlock.character c, RealBlock.induced d] 1 (-1) *
        realPositionCharacter [RealBlock.character c, RealBlock.induced d] (1 + 1) (-1)
  · have hw : k ∈ window d.weight.natAbs := by
      refine mem_window.mpr ⟨habs ▸ hk, ?_⟩
      have hpar' : (-1 : ℂ) ^ k = (-1 : ℂ) ^ (d.weight.natAbs + 1) := by
        simpa [realPositionCharacter, realInducedFirstCharacter, realInducedSecondCharacter]
          using hpar
      by_contra hne
      have hodd : Odd (k + d.weight.natAbs + 1) := Int.not_even_iff_odd.mp hne
      have h1 : (-1 : ℂ) ^ (k + d.weight.natAbs + 1) = -1 := hodd.neg_one_zpow
      rw [add_assoc, zpow_add₀ (by norm_num), hpar',
        show ((d.weight.natAbs : ℤ) + 1) = ((d.weight.natAbs + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow] at h1
      norm_num at h1
    refine blockFourierCoefficient_window_eq_zero h hf.1
      (isExpEquivariant_of_mem_principalSeries
        (τ := fun i => realPositionExponent [RealBlock.character c, RealBlock.induced d] i)
        (fun i x => realPositionCharacter_exp _ i x) hf) ?_ (fun k' hk' j hj => ?_) g k hw
    · simp [ia, ib, realPositionExponent]
      ring
    · exact hK j (habs ▸ (mem_window.mp hj).1) k' hk'
  · exact blockFourierCoefficient_eq_zero_of_parity h
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) hf hpar g

/-- The position characters take real values `±1` at signs. -/
theorem conj_realPositionCharacter_signUnit (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    conj (realPositionCharacter ds i (signUnit x)) = realPositionCharacter ds i (signUnit x) := by
  unfold signUnit
  split_ifs
  · rw [RealStrictCharacterLanglandsQuotient.realPositionCharacter_one, map_one]
  · rcases RealStrictCharacterLanglandsQuotient.realPositionCharacter_neg_one ds i with h | h <;>
      rw [h] <;> simp

theorem conj_principalSeriesCharacter_signUnit (ds : List RealBlock) (a : Fin N → ℝˣ) :
    conj (principalSeriesCharacter ℝ N (realPositionCharacter ds) (fun i => signUnit (a i))) =
      principalSeriesCharacter ℝ N (realPositionCharacter ds) (fun i => signUnit (a i)) := by
  rw [JacquetKernel.principalSeriesCharacter_sign, map_prod]
  exact Finset.prod_congr rfl fun i _ => conj_realPositionCharacter_signUnit ds i (a i)

/-! ## Positivity -/

/-- A continuous function `G` with `∫_{O(N)} G conj(G) = 0` vanishes on `O(N)`. -/
theorem eq_zero_of_integral_mul_conj {G : Langlands.GeneralLinear N ℝ → ℂ} (hG : Continuous G)
    (h : ∫ k, G (k : Langlands.GeneralLinear N ℝ) * conj (G (k : Langlands.GeneralLinear N ℝ))
      ∂haarK N = 0)
    {x : Langlands.GeneralLinear N ℝ} (hx : x ∈ unitaryCompact ℝ N) : G x = 0 := by
  by_contra hne
  have hint : (fun k : unitaryCompact ℝ N => G (k : Langlands.GeneralLinear N ℝ) *
      conj (G (k : Langlands.GeneralLinear N ℝ))) =
      fun k : unitaryCompact ℝ N => ((‖G (k : Langlands.GeneralLinear N ℝ)‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [Complex.mul_conj', Complex.ofReal_pow]
  rw [hint, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hc : Continuous fun k : unitaryCompact ℝ N => ‖G (k : Langlands.GeneralLinear N ℝ)‖ ^ 2 :=
    ((continuous_comp_val hG).norm).pow 2
  refine (hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ⟨x, hx⟩)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_).ne' h
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/-! ## High modes after two block multipliers -/

/-- **High modes after two block multipliers.** Assume the landing statement
`RealSwapLandingCharacterFirstStatement`. Let `c`, `d`, `ℓ = |d.weight|`, `δ`, `μ₀`, `μ₁` be as
there, and `e ∈ ℕ`. Let `f, g₁, g, G` be continuous right `O(3)`-finite functions on `GL_3(ℝ)`
such that, on `O(3)`:

* `Φ⁰_j f = 0` for `|j| ≥ ℓ`;
* `Φ¹_j g₁ = μ₁ j · Φ¹_j f` and `Φ⁰_j g = μ₀ j · Φ⁰_j g₁` for all `j`;
* `Φ¹_j G = Φ¹_j g` for `|j| ≥ ℓ` and `Φ¹_j G = 0` for `|j| < ℓ`;

and such that `G(diag(sgn a) κ) = χ(sgn a) · sgnDet(diag(sgn a))^e · G(κ)` for `a ∈ (ℝˣ)³`,
`κ ∈ O(3)`, where `χ` is the principal series character of the position characters of
`[c, d]`. Then `Φ¹_j g = 0` on `O(3)` for `|j| ≥ ℓ`. -/
theorem highModes_eq_zero (hL : RealSwapLandingCharacterFirstStatement)
    (c : RealCharacterData) (d : ComplexCharacterData) (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ)
    (hμ₀r : IsRecurrent δ ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀)
    (hμ₀s : IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀)
    (hμ₁r : IsRecurrent (δ + (d.weight.natAbs : ℂ)) (c.parity.val : ℤ) μ₁)
    (hμ₁s : IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁) (e : ℕ)
    {f g₁ g G : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : Continuous f) (hg₁ : Continuous g₁) (hg : Continuous g) (hG : Continuous G)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hg₁K : g₁ ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hGK : G ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3))
    (hf0 : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j f x = 0)
    (h₁ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j g₁ x = μ₁ j * blockFourierCoefficient 3 1 j f x)
    (h₀ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 j g x = μ₀ j * blockFourierCoefficient 3 0 j g₁ x)
    (hGhigh : ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j G x = blockFourierCoefficient 3 1 j g x)
    (hGlow : ∀ j : ℤ, |j| < |d.weight| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j G x = 0)
    (hGM : ∀ (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ),
      G (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
        principalSeriesCharacter ℝ 3
            (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
            (fun i => signUnit (a i)) *
          sgnDet 3 (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)))) ^ e *
            G (Unitary.toUnits κ)) :
    ∀ j : ℤ, |d.weight| ≤ |j| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j g x = 0 := by
  have hp0 : (0 : ℕ) + 1 < 3 := by norm_num
  have hp1 : (1 : ℕ) + 1 < 3 := by norm_num
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  -- the twisted projection `G' = G · sgnDet^e` and the function `φ = conj ∘ G'` on `O(3)`
  set G' : Langlands.GeneralLinear 3 ℝ → ℂ := fun x => G x * sgnDet 3 x ^ e with hG'def
  have hG'c : Continuous G' := continuous_mul_sgnDet_pow hG e
  have hG'K := mem_kFiniteVectors_mul_sgnDet_pow hGK e
  obtain ⟨P, hP⟩ :=
    OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hG'c hG'K 1
  set φ : Matrix.unitaryGroup (Fin 3) ℝ → ℂ := fun κ => conj (G' (Unitary.toUnits κ))
    with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin 3) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
    exact JacquetKernel.conj_eval_ofReal P (fun ij => (κ : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2)
  have hφc : Continuous φ :=
    Complex.continuous_conj.comp (hG'c.comp continuous_unitary_toUnits)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k))) := by
    have h := TranslateFinite.finiteDimensional_span_eval (n := 3)
      (MvPolynomial.map (starRingEnd ℂ) P)
    have heq : (fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h
  have hφM : ∀ (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
          (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    have key : G' (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ)) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
          (fun i => signUnit (a i)) * G' (Unitary.toUnits κ) := by
      simp only [hG'def]
      rw [hGM, MonoidHom.map_mul, sgnDet_mul, mul_pow]
      linear_combination (principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.character c, RealBlock.induced d])
          (fun i => signUnit (a i)) * G (Unitary.toUnits κ) *
            sgnDet 3 (Unitary.toUnits κ) ^ e) *
        sgnDet_pow_mul_self e (Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))))
    simp only [hφdef]
    rw [key, map_mul, conj_principalSeriesCharacter_signUnit]
  -- the test function `t ∈ [c, d]` with `t = conj G'` on `O(3)`
  obtain ⟨t, htK, htval⟩ := principalSeriesExtension 3
    [RealBlock.character c, RealBlock.induced d] φ hφc hfin hφM
  have htc : Continuous t := JacquetKernel.continuous_of_mem htK
  have hval : ∀ x ∈ unitaryCompact ℝ 3, t x = conj (G' x) := by
    intro x hx
    have hk : x = Unitary.toUnits
        (⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩ : Matrix.unitaryGroup (Fin 3) ℝ) := Units.ext rfl
    rw [hk, htval]
  have htlow : ∀ j : ℤ, |j| < |d.weight| → ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 1 j t x = 0 := by
    intro j hj x hx
    rw [blockFourierCoefficient_congr hval 1 j hx, blockFourierCoefficient_conj, hG'def,
      blockFourierCoefficient_mul_sgnDet_pow, hGlow (-j) (by rwa [abs_neg]) x hx, mul_zero,
      map_zero]
  have htmem : t ∈ kFiniteFunctions
      (realStandardModule 3 [RealBlock.character c, RealBlock.induced d]) (unitaryCompact ℝ 3) :=
    ⟨mem_realStandardModule_character_induced c d htK.1 htlow, htK.2⟩
  -- the reflected multipliers applied to `t`, and the landing statement
  obtain ⟨t₀, ht₀c, ht₀K, ht₀⟩ := exists_multiplier hp0 htc htK.2 (fun j => μ₀ (-j))
  obtain ⟨u, huc, huK, hu⟩ := exists_multiplier hp1 ht₀c ht₀K (fun j => μ₁ (-j))
  have hland := hL c d δ (fun j => μ₀ (-j)) (fun j => μ₁ (-j)) t t₀ u
    (isRecurrent_comp_neg hμ₀r) (isSymmetric_comp_neg (neg_one_pow_mul_self _) hμ₀s)
    (isRecurrent_comp_neg hμ₁r) (isSymmetric_comp_neg (neg_one_pow_mul_self _) hμ₁s) htmem
    ht₀c huc (fun x hx k => ht₀ k x hx) (fun x hx k => hu k x hx)
  -- the twisted test functions
  have hψc := continuous_mul_sgnDet_pow htc e
  have hψ₀c := continuous_mul_sgnDet_pow ht₀c e
  have hψ₁c := continuous_mul_sgnDet_pow huc e
  have hψK := mem_kFiniteVectors_mul_sgnDet_pow htK.2 e
  have hψ₀K := mem_kFiniteVectors_mul_sgnDet_pow ht₀K e
  have hψ₁K := mem_kFiniteVectors_mul_sgnDet_pow huK e
  -- `∫ g ψ = ∫ g₁ ψ₀ = ∫ f ψ₁ = 0`
  have i₁ := integral_mul_eq_of_multiplier hp0 hg₁ hg hψc hψ₀c hg₁K hgK hψK hψ₀K μ₀ h₀
    (fun j x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, blockFourierCoefficient_mul_sgnDet_pow,
        ht₀ j x hx]
      ring)
  have i₂ := integral_mul_eq_of_multiplier hp1 hf hg₁ hψ₀c hψ₁c hfK hg₁K hψ₀K hψ₁K μ₁ h₁
    (fun j x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, blockFourierCoefficient_mul_sgnDet_pow,
        hu j x hx]
      ring)
  have i₃ := integral_mul_eq_zero_of_modes hp0 hψ₁c hf hψ₁K hfK d.weight.natAbs
    (fun j hj x hx => by
      rw [blockFourierCoefficient_mul_sgnDet_pow, hland x hx j (habs ▸ hj), mul_zero])
    (fun j hj x hx => hf0 j (habs ▸ hj) x hx)
  -- `∫ G ψ = ∫ g ψ` by the transposition with the indicator of the high modes
  have i₄ := integral_mul_eq_of_multiplier hp1 hg hG hψc hψc hgK hGK hψK hψK
    (fun j => if |d.weight| ≤ |j| then 1 else 0)
    (fun j x hx => by
      by_cases hj : |d.weight| ≤ |j|
      · rw [ite_eq_left hj, one_mul, hGhigh j hj x hx]
      · rw [ite_eq_right hj, zero_mul, hGlow j (not_le.mp hj) x hx])
    (fun j x hx => by
      rw [abs_neg]
      by_cases hj : |d.weight| ≤ |j|
      · rw [ite_eq_left hj, one_mul]
      · rw [ite_eq_right hj, zero_mul, blockFourierCoefficient_mul_sgnDet_pow,
          htlow j (not_le.mp hj) x hx, mul_zero])
  -- `ψ = conj G` on `O(3)`
  have hψG : ∀ x ∈ unitaryCompact ℝ 3, t x * sgnDet 3 x ^ e = conj (G x) := by
    intro x hx
    rw [hval x hx]
    simp only [hG'def, map_mul, map_pow, conj_sgnDet]
    rw [mul_assoc, sgnDet_pow_mul_self, mul_one]
  have hint : ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) *
      conj (G (k : Langlands.GeneralLinear 3 ℝ)) ∂haarK 3 = 0 := by
    calc ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) * conj (G (k : Langlands.GeneralLinear 3 ℝ))
          ∂haarK 3
        = ∫ k, G (k : Langlands.GeneralLinear 3 ℝ) *
            (t (k : Langlands.GeneralLinear 3 ℝ) *
              sgnDet 3 (k : Langlands.GeneralLinear 3 ℝ) ^ e) ∂haarK 3 :=
          integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hψG _ k.2])
      _ = _ := i₄
      _ = _ := i₁
      _ = _ := i₂
      _ = ∫ k, (u (k : Langlands.GeneralLinear 3 ℝ) *
            sgnDet 3 (k : Langlands.GeneralLinear 3 ℝ) ^ e) *
              f (k : Langlands.GeneralLinear 3 ℝ) ∂haarK 3 :=
          integral_congr_ae (Filter.Eventually.of_forall fun k => mul_comm _ _)
      _ = 0 := i₃
  have hG0 : ∀ x ∈ unitaryCompact ℝ 3, G x = (fun _ => (0 : ℂ)) x :=
    fun x hx => eq_zero_of_integral_mul_conj hG hint hx
  intro j hj x hx
  rw [← hGhigh j hj x hx, blockFourierCoefficient_congr hG0 1 j hx]
  simp [blockFourierCoefficient]

end RealSwapFLanding

end Langlands.Archimedean
