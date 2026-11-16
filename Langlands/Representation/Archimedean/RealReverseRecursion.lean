import Langlands.Representation.Archimedean.RealBlockSliceDecomposition
import Langlands.Representation.Archimedean.RealBlockLimitValue
import Langlands.Representation.Archimedean.RealBlockFunctional
import Langlands.Representation.Archimedean.RealReverseTwist

/-!
# The transposed-coefficient recursion for the block Jacquet functional

For `x` in the principal series of `χ⁻¹` and `y` in that of `χ` on `GL_n(ℝ)` let
`coeff x y (g) = ∫_{O(n)} x(κ g) y(κ) dκ`. For a space `U` of functions of the principal series of
`χ⁻¹`, `nullCoeff χ U` is the span of the coefficients `coeff x y` with `y` orthogonal to `U`.

The main theorem `jac_eq_zero_of_transpose` (by induction on the block decomposition `ks`):
if `U` is nonzero and `(𝔤, K)`-stable, `X` is `(𝔤, K)`-stable, and for every `x ∈ X` the function
`g ↦ coeff x f (gᵀ)` lies in `nullCoeff χ U`, then `x(1) · jac ks e p f = 0` for all `x ∈ X`.

The induction step evaluates along `g = d(s) diag(g₁, 1)` with `d(s) = diag(1_a, s·1_{k+1})`,
normalizes by the value-form limit `RealBlockLimitValue.exists_tendsto`, and identifies the limits
on both sides: on the left after replacing `x` by `x'` with `x'(diag(h, g₂)) = x(diag(h, 1)) φ(g₂)`
(`RealBlockSliceDecomposition.exists_mem_blockDiag_eq`, `φ` the block vector), on the right through
the finite separation of variables `RealBlockSliceDecomposition.exists_blockDiag_decomposition`
and the dual step `RealBlockDual.integral_restrictBlock_mul_blockPair_eq_zero`.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealReverseRecursion

open RealBlockParabolic RealBlockChart RealBlockLimit RealBlockJacquet RealBlockDual
  RealBlockFunctional RealBlockLimitValue RealBlockSliceDecomposition PartialJacquet
  JacquetLimit GramFormula PrincipalSeriesExtension RealPrincipalSeriesDuality RealReverseTwist

attribute [local instance] measurableSpaceK secondCountableTopology_unitaryCompact

/-! ## Transpose -/

section Transpose

variable {a k : ℕ}

theorem blockDiag_transpose (A : Matrix (Fin a) (Fin a) ℝ) (D : Matrix (Fin k) (Fin k) ℝ) :
    (RealBlockParabolic.blockDiag A D)ᵀ = RealBlockParabolic.blockDiag Aᵀ Dᵀ := by
  rw [RealBlockParabolic.blockDiag, RealBlockParabolic.blockDiag, Matrix.transpose_reindex,
    Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero]

theorem transposeGL_blockDiagGL (g₁ : Langlands.GeneralLinear a ℝ)
    (g₂ : Langlands.GeneralLinear k ℝ) :
    transposeGL (blockDiagGL g₁ g₂) = blockDiagGL (transposeGL g₁) (transposeGL g₂) := by
  apply Units.ext
  rw [transposeGL_val, blockDiagGL_val, blockDiagGL_val, transposeGL_val, transposeGL_val,
    blockDiag_transpose]

theorem transposeGL_dTail (s : ℝˣ) :
    transposeGL (dTail (a := a) (k := k) s) = dTail s := by
  apply Units.ext
  rw [transposeGL_val, dTail_val, tailMat, blockDiag_transpose, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_one]

/-- `(d(s) diag(g₁, 1))ᵀ = d(s) diag(g₁ᵀ, 1)`. -/
theorem transposeGL_dTail_mul (s : ℝˣ) (g₁ : Langlands.GeneralLinear a ℝ) :
    transposeGL (dTail (a := a) (k := k) s * blockDiagGL g₁ 1) =
      dTail s * blockDiagGL (transposeGL g₁) 1 := by
  rw [transposeGL_mul, transposeGL_blockDiagGL, transposeGL_one, transposeGL_dTail,
    blockDiagGL_mul_dTail]

end Transpose

/-! ## Matrix coefficients and null coefficients -/

section Coefficients

variable {n : ℕ}

/-- The matrix coefficient `g ↦ ∫_{O(n)} x(κ g) y(κ) dκ`. -/
def coeff (x y : Langlands.GeneralLinear n ℝ → ℂ) (g : Langlands.GeneralLinear n ℝ) : ℂ :=
  ∫ κ, x ((κ : Langlands.GeneralLinear n ℝ) * g) * y κ ∂haarK n

/-- The span of the coefficients `coeff x y` with `x` an `O(n)`-finite function of the principal
series of `χ⁻¹` and `y` an `O(n)`-finite function of the principal series of `χ` orthogonal to
`U`. -/
def nullCoeff (χ : ℕ → ℝˣ → ℂ) (U : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) :
    Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  Submodule.span ℂ {F | ∃ x y : Langlands.GeneralLinear n ℝ → ℂ,
    x ∈ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) ∧
    y ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) ∧
    (∀ u ∈ U, ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) * y κ ∂haarK n = 0) ∧ F = coeff x y}

end Coefficients

/-! ## The limit of coefficients along `d(s)` -/

section Limit

variable {a k : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem coeff_dTail_mul (x y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ) (s : ℝˣ)
    (g₁ : Langlands.GeneralLinear a ℝ) :
    coeff x y (dTail (a := a) (k := k + 1) s * blockDiagGL g₁ 1) =
      ∫ κ, Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ)
        (blockDiagGL g₁ 1) x ((κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) * dTail s) * y κ
        ∂haarK (a + (k + 1)) := by
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  change x (_ * (_ * _)) * _ = x (_ * _ * _) * _
  rw [mul_assoc]

/-- The limit value of a right translate by `diag(g₁, 1)` of a function with a finite separation
of variables `x(diag(h, g₂)) = ∑ᵢ rᵢ(h) bᵢ(g₂)`. -/
theorem limitValue_rightTranslation (hT1 : RealBlockChartIntegrableStatement)
    (hχ : IsSignedPower χ e) (he : IsBlockDominant e a k) {ι : Type} [Fintype ι]
    {x : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    {r : ι → Langlands.GeneralLinear a ℝ → ℂ} {b : ι → Langlands.GeneralLinear (k + 1) ℝ → ℂ}
    (hr : ∀ i, Continuous (r i)) (hb : ∀ i, Continuous (b i))
    (hx : ∀ (h : Langlands.GeneralLinear a ℝ) (g₂ : Langlands.GeneralLinear (k + 1) ℝ),
      x (blockDiagGL h g₂) = ∑ i, r i h * b i g₂)
    {y : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ}
    (hy : y ∈ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) χ)
      (unitaryCompact ℝ (a + (k + 1))))
    (g₁ : Langlands.GeneralLinear a ℝ) :
    limitValue (a := a) (k := k) (Whittaker.rightTranslation ℂ
      (Langlands.GeneralLinear (a + (k + 1)) ℝ) (blockDiagGL g₁ 1) x) y =
      ∑ i, coeff (r i) (blockPair (b i) y) g₁ := by
  have hstep : ∀ κ₁ : unitaryCompact ℝ a, Continuous fun κ₂ : unitaryCompact ℝ (k + 1) =>
      blockStep y (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
        (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) := fun κ₁ =>
    continuous_blockStep hT1 hχ he hy.1 (f₁ := fun _ => (κ₁ : Langlands.GeneralLinear a ℝ))
      continuous_const continuous_subtype_val (fun _ => κ₁.2) (fun t => t.2)
  have hinner : ∀ κ₁ : unitaryCompact ℝ a,
      (∫ κ₂ : unitaryCompact ℝ (k + 1), Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear (a + (k + 1)) ℝ) (blockDiagGL g₁ 1) x
          (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) *
        blockStep y (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) ∂haarK (k + 1)) =
      ∑ i, r i ((κ₁ : Langlands.GeneralLinear a ℝ) * g₁) * blockPair (b i) y κ₁ := by
    intro κ₁
    have hpt : ∀ κ₂ : unitaryCompact ℝ (k + 1), Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear (a + (k + 1)) ℝ) (blockDiagGL g₁ 1) x
          (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) *
        blockStep y (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)) =
        ∑ i, r i ((κ₁ : Langlands.GeneralLinear a ℝ) * g₁) * (b i κ₂ *
          blockStep y (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℝ))) := by
      intro κ₂
      change x (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
        (κ₂ : Langlands.GeneralLinear (k + 1) ℝ) * blockDiagGL g₁ 1) * _ = _
      rw [← blockDiagGL_mul, mul_one, hx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum (f := fun i
      (κ₂ : unitaryCompact ℝ (k + 1)) => r i ((κ₁ : Langlands.GeneralLinear a ℝ) * g₁) *
        (b i κ₂ * blockStep y (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℝ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℝ)))) _ fun i _ =>
      (integrable_of_continuous (((hb i).comp continuous_subtype_val).mul
        (hstep κ₁))).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    rfl
  rw [limitValue, integral_congr_ae (ae_of_all _ hinner), integral_finsetSum (f := fun i
      (κ₁ : unitaryCompact ℝ a) => r i ((κ₁ : Langlands.GeneralLinear a ℝ) * g₁) *
        blockPair (b i) y κ₁) _ fun i _ =>
    integrable_of_continuous (((hr i).comp (continuous_subtype_val.mul continuous_const)).mul
      ((blockPair_mem hT1 hχ he hy (hb i)).1.1.continuous.comp continuous_subtype_val))]
  rfl

/-- The value-form limit with constant `c` (the conclusion of
`RealBlockLimitValue.exists_tendsto`). -/
def IsLimitConstant (a k : ℕ) (c : ℂ) : Prop :=
  ∀ {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e → IsBlockDominant e a k →
    ∀ {u h : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ},
    u ∈ principalSeries ℝ (a + (k + 1)) (dualChar χ) →
    h ∈ principalSeries ℝ (a + (k + 1)) χ →
      Tendsto (fun m : ℕ => (c * tailFactor a k χ (seqUnit m))⁻¹ *
        ∫ κ, u ((κ : Langlands.GeneralLinear (a + (k + 1)) ℝ) * dTail (seqUnit m)) * h κ
          ∂haarK (a + (k + 1))) atTop (𝓝 (limitValue u h))

/-- **Limits of null coefficients.** Every `F ∈ nullCoeff χ U` has, after normalization, a limit
along `d(s_m) diag(g₁, 1)` which is a null coefficient of the restriction of `U` to `GL_a(ℝ)`. -/
theorem exists_tendsto_nullCoeff (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (hχ : IsSignedPower χ e)
    (he : IsBlockDominant e a k)
    (hirrT : IsIrreducibleGKModule (principalSeriesRep ℝ (k + 1) (blockDualChar a χ))
      (principalSeriesLie ℝ (k + 1) (blockDualChar a χ)))
    {c : ℂ} (hc : IsLimitConstant a k c)
    {U : Submodule ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ)}
    (hU : U ≤ kFiniteFunctions (principalSeries ℝ (a + (k + 1)) (dualChar χ))
      (unitaryCompact ℝ (a + (k + 1))))
    (hUK : ∀ κ ∈ unitaryCompact ℝ (a + (k + 1)), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (a + (k + 1)) ℝ) κ u ∈ U)
    (hUD : ∀ (Y : Matrix (Fin (a + (k + 1))) (Fin (a + (k + 1))) ℝ), ∀ u ∈ U,
      rightDerivative (matrixModel ℝ (a + (k + 1))) Y u ∈ U)
    {F : Langlands.GeneralLinear (a + (k + 1)) ℝ → ℂ} (hF : F ∈ nullCoeff χ U) :
    ∃ G ∈ nullCoeff (blockShiftChar k χ) (U.map (restrictBlock (k := k))),
      ∀ g₁ : Langlands.GeneralLinear a ℝ,
        Tendsto (fun m : ℕ => (c * tailFactor a k χ (seqUnit m))⁻¹ *
          F (dTail (a := a) (k := k + 1) (seqUnit m) * blockDiagGL g₁ 1)) atTop (𝓝 (G g₁)) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨x, y, hx, hy, hyU, rfl⟩ := hF
    obtain ⟨ι, _, yt, b, hyt, hb, hdec⟩ :=
      exists_blockDiag_decomposition hχ (χT := blockDualChar a χ) (fun _ _ _ => rfl) hx
    refine ⟨∑ i, coeff (restrictBlock (k := k) (yt i)) (blockPair (b i) y),
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, _, restrictBlock_mem hχ (hyt i),
        blockPair_mem hT1 hχ he hy (hb i).1.1.continuous, ?_, rfl⟩, fun g₁ => ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact integral_restrictBlock_mul_blockPair_eq_zero hT1 hT3 hχ he (fun _ _ _ => rfl) hirrT
        hU hUK hUD hy hyU ⟨b i, hb i⟩ hu
    · have hlim := hc hχ he (rightTranslation_mem_principalSeries _ hx.1 (blockDiagGL g₁ 1))
        hy.1
      rw [limitValue_rightTranslation hT1 hχ he
        (fun i => (restrictBlock_mem hχ (hyt i)).1.1.continuous)
        (fun i => (hb i).1.1.continuous) hdec hy g₁] at hlim
      rw [Finset.sum_apply]
      exact hlim.congr fun m => by rw [coeff_dTail_mul]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun g₁ => ?_⟩
    simp only [Pi.zero_apply, mul_zero]
    exact tendsto_const_nhds
  | add F₁ F₂ _ _ h₁ h₂ =>
    obtain ⟨G₁, hG₁, hl₁⟩ := h₁
    obtain ⟨G₂, hG₂, hl₂⟩ := h₂
    refine ⟨G₁ + G₂, add_mem hG₁ hG₂, fun g₁ => ?_⟩
    simp only [Pi.add_apply, mul_add]
    exact (hl₁ g₁).add (hl₂ g₁)
  | smul r F _ h =>
    obtain ⟨G, hG, hl⟩ := h
    refine ⟨r • G, Submodule.smul_mem _ r hG, fun g₁ => ?_⟩
    have := (hl g₁).const_mul r
    simp only [Pi.smul_apply, smul_eq_mul]
    exact this.congr fun m => by ring

end Limit

/-! ## The recursion -/

/-- **The transposed-coefficient recursion.** Assume the block statements and `TiedIrreducible`.
Let `ks` be a block decomposition with `BlockOrdered ks e`, `U` a nonzero and `X` an arbitrary
`(𝔤, K)`-stable space of `O(n)`-finite functions of the principal series of `χ⁻¹`, and `f` an
`O(n)`-finite function of the principal series of `χ`. If `g ↦ coeff x f (gᵀ)` lies in
`nullCoeff χ U` for every `x ∈ X`, then `x(1) · jac ks e p f = 0` for every `x ∈ X`. -/
theorem jac_eq_zero_of_transpose (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement) (hirr : TiedIrreducible) :
    ∀ (ks : List ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (p : ℕ → ℕ), IsSignedPower χ e →
    (∀ l : ℕ, χ l (-1) = (-1) ^ p l) →
    BlockOrdered ks e →
    ∀ {U : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℝ → ℂ)},
    U ≤ kFiniteFunctions (principalSeries ℝ (dim ks) (dualChar χ)) (unitaryCompact ℝ (dim ks)) →
    (∀ κ ∈ unitaryCompact ℝ (dim ks), ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℝ) κ u ∈ U) →
    (∀ (Y : Matrix (Fin (dim ks)) (Fin (dim ks)) ℝ), ∀ u ∈ U,
      rightDerivative (matrixModel ℝ (dim ks)) Y u ∈ U) →
    U ≠ ⊥ →
    ∀ {X : Submodule ℂ (Langlands.GeneralLinear (dim ks) ℝ → ℂ)},
    X ≤ kFiniteFunctions (principalSeries ℝ (dim ks) (dualChar χ)) (unitaryCompact ℝ (dim ks)) →
    (∀ κ ∈ unitaryCompact ℝ (dim ks), ∀ x ∈ X,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (dim ks) ℝ) κ x ∈ X) →
    (∀ (Y : Matrix (Fin (dim ks)) (Fin (dim ks)) ℝ), ∀ x ∈ X,
      rightDerivative (matrixModel ℝ (dim ks)) Y x ∈ X) →
    ∀ {f : Langlands.GeneralLinear (dim ks) ℝ → ℂ},
    f ∈ kFiniteFunctions (principalSeries ℝ (dim ks) χ) (unitaryCompact ℝ (dim ks)) →
    (∀ x ∈ X, (fun g => coeff x f (transposeGL g)) ∈ nullCoeff χ U) →
    ∀ x ∈ X, x 1 * jac ks e p f = 0
  | [], χ, e, p, _, _, _, U, _, _, _, hU0, X, _, _, _, f, _, hH, x, hx => by
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      have hsub : ∀ g : Langlands.GeneralLinear (dim []) ℝ, g = 1 := fun g => by
        apply Units.ext
        ext i j
        exact i.elim0
      have hu1 : u 1 ≠ 0 := fun h1 => hu0 (funext fun g => by rw [hsub g]; exact h1)
      have hbot : nullCoeff χ U = ⊥ := by
        rw [eq_bot_iff, nullCoeff, Submodule.span_le]
        rintro _ ⟨x', y, -, -, hy, rfl⟩
        have hint := hy u huU
        have hconst : (fun κ : unitaryCompact ℝ (dim []) =>
            u (κ : Langlands.GeneralLinear (dim []) ℝ) * y κ) = fun _ => u 1 * y 1 :=
          funext fun κ => by rw [hsub κ]
        rw [hconst, integral_const, probReal_univ, one_smul] at hint
        have hy1 : ∀ g : Langlands.GeneralLinear (dim []) ℝ, y g = 0 := fun g => by
          rw [hsub g]
          exact (mul_eq_zero.mp hint).resolve_left hu1
        refine (Submodule.mem_bot ℂ).mpr (funext fun g => ?_)
        simp only [coeff, hy1, mul_zero, integral_zero, Pi.zero_apply]
      have h1 : coeff x f (transposeGL 1) = 0 := by
        have h := hH x hx
        rw [hbot, Submodule.mem_bot] at h
        exact congrFun h 1
      have hc : coeff x f (transposeGL 1) = x 1 * f 1 := by
        rw [coeff]
        have hconst : (fun κ : unitaryCompact ℝ (dim []) =>
            x ((κ : Langlands.GeneralLinear (dim []) ℝ) * transposeGL 1) * f κ) =
            fun _ => x 1 * f 1 :=
          funext fun κ => by
            rw [hsub ((κ : Langlands.GeneralLinear (dim []) ℝ) * transposeGL 1),
              hsub (κ : Langlands.GeneralLinear (dim []) ℝ)]
        rw [hconst, integral_const, probReal_univ, one_smul]
      change x 1 * f 1 = 0
      rw [← hc, h1]
  | k :: ks, χ, e, p, hχ, hp, ⟨he, hks⟩, U, hU, hUK, hUD, hU0, X, hX, hXK, hXD, f, hf, hH,
      x, hx => by
      have hφ := blockVector_mem hχ hp (dim ks) k
      have hirrT := hirr (k + 1) (blockDualChar (dim ks) χ)
        (fun l => -(e (dim ks + l)) - ((dim ks : ℕ) : ℂ) / 2) (fun l => p (dim ks + l))
        (isSignedPower_blockDualChar hχ (dim ks)) (blockDualChar_neg_one hp (dim ks))
        (fun l hl => by
          simp only [Complex.sub_re, Complex.neg_re, add_zero]
          rw [he.tie l (by omega)])
      obtain ⟨hUM, hUMK, hUMD, hUM0⟩ := map_restrictBlock (k := k) hχ hU hUK hUD hU0
      by_cases hX0 : X = ⊥
      · rw [hX0, Submodule.mem_bot] at hx
        rw [hx, Pi.zero_apply, zero_mul]
      obtain ⟨hXM, hXMK, hXMD, -⟩ := map_restrictBlock (k := k) hχ hX hXK hXD hX0
      obtain ⟨c, -, hc⟩ := exists_tendsto hT1 hT3 (dim ks) k
      have hIH := jac_eq_zero_of_transpose hT1 hT3 hirr ks p (isSignedPower_blockShift hχ)
        (blockShiftChar_neg_one k hp) (hks.shift _) hUM hUMK hUMD hUM0 hXM hXMK hXMD
        (blockPair_mem hT1 hχ he hf hφ.1.1.continuous) ?_ (restrictBlock (k := k) x)
        ⟨x, hx, rfl⟩
      · rw [jac_cons]
        rwa [restrictBlock_apply, blockDiagGL_one_one] at hIH
      · rintro _ ⟨x₀, hx₀, rfl⟩
        obtain ⟨x', hx'X, hx'⟩ := exists_mem_blockDiag_eq hχ (fun _ _ _ => rfl) hirrT hX hXK hXD
          hx₀ ⟨_, hφ⟩
        obtain ⟨G, hG, hGlim⟩ := exists_tendsto_nullCoeff hT1 hT3 hχ he hirrT hc hU hUK hUD
          (hH x' hx'X)
        convert hG using 1
        funext g₁
        refine tendsto_nhds_unique ?_ (hGlim g₁)
        have hlim := hc hχ he (rightTranslation_mem_principalSeries _ (hX hx'X).1
          (blockDiagGL (transposeGL g₁) 1)) hf.1
        have hval : limitValue (a := dim ks) (k := k) (Whittaker.rightTranslation ℂ
            (Langlands.GeneralLinear (dim (k :: ks)) ℝ) (blockDiagGL (transposeGL g₁) 1) x')
            f = coeff (restrictBlock (k := k) x₀)
              (blockPair (blockVector (dim ks) k e p) f) (transposeGL g₁) :=
          (limitValue_rightTranslation hT1 hχ he (ι := Unit)
            (r := fun _ => restrictBlock (k := k) x₀) (b := fun _ => blockVector (dim ks) k e p)
            (fun _ => (restrictBlock_mem hχ (hX hx₀)).1.1.continuous)
            (fun _ => hφ.1.1.continuous)
            (fun h g₂ => by rw [Fintype.sum_unique]; exact hx' h g₂)
            hf (transposeGL g₁)).trans (Fintype.sum_unique _)
        rw [hval] at hlim
        refine hlim.congr fun m => ?_
        rw [transposeGL_dTail_mul, coeff_dTail_mul]
        rfl

end RealReverseRecursion

end Langlands.Archimedean
