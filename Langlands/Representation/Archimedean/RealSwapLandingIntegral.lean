import Langlands.Representation.Archimedean.RealSwapLandingMatrices
import Langlands.Representation.Archimedean.RealSwapLandingAlgebra

/-!
# The landing integral for the blocks `[induced d, character c]`

See the companion Markdown file.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

namespace RealSwapLandingIntegral

open RealSwapLandingKernel RealSwapLandingRankOne RealSwapLandingMatrices RealBlockRotation
  MaximalParabolicIntegration PartialJacquet RealJacquetFrobenius Langlands.LocalFactor.Archimedean
  RealBlockFourierFinite RealBlockPropagation RealBlockDerivative PrincipalSeriesExtension
  GramFormula

/-! ## Membership in the standard module of `[induced d, character c]` -/

/-- The only induction block of `[d, c]` starts at position `0` and is `d`. -/
theorem realInducedBlockAt_induced_character (d : ComplexCharacterData) (c : RealCharacterData)
    {p : ℕ} {d' : ComplexCharacterData}
    (h : realInducedBlockAt [RealBlock.induced d, RealBlock.character c] p = some d') :
    p = 0 ∧ d' = d := by
  rcases p with _ | _ | _ | p
  · simp only [realInducedBlockAt, Option.some.injEq] at h
    exact ⟨rfl, h.symm⟩
  · simp [realInducedBlockAt] at h
  · simp [realInducedBlockAt] at h
  · simp [realInducedBlockAt] at h

/-- **Membership in the standard module of `[d, c]`.** A function of the principal series of
the position characters of `[d, c]` whose Fourier coefficients of weight `|k| < |m|` along
`r_0` vanish on `O(3)` lies in the standard module of `[d, c]`. -/
theorem mem_realStandardModule_induced_character (d : ComplexCharacterData)
    (c : RealCharacterData) {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ 3
      (realPositionCharacter [RealBlock.induced d, RealBlock.character c]))
    (hK : ∀ k : ℤ, |k| < |d.weight| → ∀ g ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 0 k f g = 0) :
    f ∈ realStandardModule 3 [RealBlock.induced d, RealBlock.character c] := by
  refine (mem_realStandardModule_iff 3 _ f).mpr ⟨hf, fun p d' hd k hk g => ?_⟩
  obtain ⟨hp, hd'⟩ := realInducedBlockAt_induced_character d c hd
  subst hp
  rw [hd'] at hk
  have h : 0 + 1 < 3 := by norm_num
  have habs : |d.weight| = (d.weight.natAbs : ℤ) := Int.abs_eq_natAbs d.weight
  by_cases hpar : (-1 : ℂ) ^ k =
      realPositionCharacter [RealBlock.induced d, RealBlock.character c] 0 (-1) *
        realPositionCharacter [RealBlock.induced d, RealBlock.character c] (0 + 1) (-1)
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
        (τ := fun i => realPositionExponent [RealBlock.induced d, RealBlock.character c] i)
        (fun i x => RealSwapFLanding.realPositionCharacter_exp _ i x) hf) ?_
      (fun k' hk' j hj => ?_) g k hw
    · simp [ia, ib, realPositionExponent]
      ring
    · exact hK j (habs ▸ (mem_window.mp hj).1) k' hk'
  · exact blockFourierCoefficient_eq_zero_of_parity h
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) hf hpar g

/-! ## Changing the exponent of the character block -/

/-- **Extension with another exponent.** For `f` in the `O(3)`-finite standard module of
`[d, c]` and any `s ∈ ℂ` there is `f'` in the `O(3)`-finite standard module of
`[d, charData (parity c) s]` with `f' = f` on `O(3)`. -/
theorem exists_extension (c : RealCharacterData) (d : ComplexCharacterData) (s : ℂ)
    {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
      (unitaryCompact ℝ 3)) :
    ∃ f' ∈ kFiniteFunctions
        (realStandardModule 3 [RealBlock.induced d, RealBlock.character (charData c.parity s)])
        (unitaryCompact ℝ 3),
      ∀ x ∈ unitaryCompact ℝ 3, f' x = f x := by
  have hfc : Continuous f := RealBlockJacquet.continuous_coe ⟨f, hf⟩
  obtain ⟨P, hP⟩ :=
    OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors hfc hf.2 1
  set φ : Matrix.unitaryGroup (Fin 3) ℝ → ℂ := fun κ => f (Unitary.toUnits κ) with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin 3) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℝ) : ℂ)) P := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
  have hφc : Continuous φ := hfc.comp continuous_unitary_toUnits
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k))) := by
    have h := TranslateFinite.finiteDimensional_span_eval (n := 3) P
    have heq : (fun k : Matrix.unitaryGroup (Fin 3) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin 3) ℝ) :
          Matrix (Fin 3) (Fin 3) ℝ) ij.1 ij.2 : ℂ)) P :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h
  have hsign : ∀ a : Fin 3 → ℝˣ,
      principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character c])
          (fun i => signUnit (a i)) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character (charData c.parity s)])
          (fun i => signUnit (a i)) := by
    intro a
    rw [JacquetKernel.principalSeriesCharacter_sign, JacquetKernel.principalSeriesCharacter_sign]
    refine Finset.prod_congr rfl fun i _ => ?_
    fin_cases i
    · rfl
    · rfl
    · change (c.character (signUnit (a 2)) : ℂ) =
        ((charData c.parity s).character (signUnit (a 2)) : ℂ)
      rw [c.character_eq, (charData c.parity s).character_eq, GramFormula.abs_signUnit,
        Complex.ofReal_one, Complex.one_cpow, Complex.one_cpow]
      rfl
  have hφM : ∀ (a : Fin 3 → ℝˣ) (κ : Matrix.unitaryGroup (Fin 3) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ 3
          (realPositionCharacter [RealBlock.induced d, RealBlock.character (charData c.parity s)])
          (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    simp only [hφdef]
    rw [PartialJacquet.signDiagonal_toUnits, hf.1.1.2, hsign]
  obtain ⟨t, htK, htval⟩ := principalSeriesExtension 3
    [RealBlock.induced d, RealBlock.character (charData c.parity s)] φ hφc hfin hφM
  have hval : ∀ x ∈ unitaryCompact ℝ 3, t x = f x := by
    intro x hx
    have hk : x = Unitary.toUnits
        (⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩ : Matrix.unitaryGroup (Fin 3) ℝ) := Units.ext rfl
    rw [hk, htval]
  refine ⟨t, ⟨mem_realStandardModule_induced_character d _ htK.1 fun k hk g hg => ?_, htK.2⟩,
    hval⟩
  rw [RealSwapFLanding.blockFourierCoefficient_congr hval 0 k hg]
  exact hf.1.2 0 d rfl k hk g

/-! ## Integrability on the chart -/

set_option backward.isDefEq.respectTransparency false in
/-- Functions of a principal series of `GL_3(ℝ)` are continuous. -/
theorem continuous_of_mem_principalSeries {χ : ℕ → ℝˣ → ℂ}
    {f : Langlands.GeneralLinear 3 ℝ → ℂ} (hf : f ∈ principalSeries ℝ 3 χ) : Continuous f :=
  hf.1.continuous

theorem continuous_rotInv : Continuous rotInv :=
  continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp [rotInv] <;> fun_prop

theorem norm_exp_neg_mul_I (k : ℤ) (θ : ℝ) :
    ‖Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

section Landing

variable {d : ComplexCharacterData} {e : Fin 2} {n : ℕ} {s : ℂ}
  {f : Langlands.GeneralLinear 3 ℝ → ℂ}

/-- For `ℓ ≥ 1` and `s = t - ℓ/2 - (n + 1)` the exponents `t + ℓ/2, t - ℓ/2, s` have strictly
decreasing real parts. -/
theorem isStrictlyDominant
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hℓ : 0 < d.weight.natAbs) :
    IsStrictlyDominant
      (realPositionExponent [RealBlock.induced d, RealBlock.character (charData e s)]) 2 := by
  have key : ((d.weight.natAbs : ℂ) / 2).re = (d.weight.natAbs : ℝ) / 2 := by simp
  have hℓ' : (0 : ℝ) < d.weight.natAbs := Nat.cast_pos.mpr hℓ
  intro l hl
  interval_cases l
  · show (d.exponent - (d.weight.natAbs : ℂ) / 2).re < (d.exponent + (d.weight.natAbs : ℂ) / 2).re
    rw [Complex.sub_re, Complex.add_re, key]
    linarith
  · show s.re < (d.exponent - (d.weight.natAbs : ℂ) / 2).re
    rw [hs, Complex.sub_re, Complex.sub_re, key, Complex.add_re, Complex.natCast_re,
      Complex.one_re]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- The integral `∫_{ℝ²} f(chartGL v · w · x) dv`. -/
def chartIntegral (f : Langlands.GeneralLinear 3 ℝ → ℂ) (x : Langlands.GeneralLinear 3 ℝ) : ℂ :=
  ∫ v : Fin 2 → ℝ, f (chartGL v * (wPerm * x))

/-- **The chart integral on `O(3)`.** `∫_{ℝ²} f(chartGL v · w · x) dv = (-1)^{ℓ+1} C⁰_{n+ℓ} C¹_n f(x)`
for `x ∈ O(3)`. -/
theorem chartIntegral_eq
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ principalSeries ℝ 3 (posChar d e s)) (hℓ : 0 < d.weight.natAbs)
    {x : Langlands.GeneralLinear 3 ℝ} (hx : x ∈ unitaryCompact ℝ 3) :
    chartIntegral f x = (-1 : ℂ) ^ (d.weight.natAbs + 1) *
      kernelOp 3 0 (n + d.weight.natAbs) (kernelOp 3 1 n f) x := by
  have hκ : wPerm * x ∈ unitaryCompact ℝ 3 :=
    Subgroup.mul_mem _ wPerm_mem_unitaryCompact hx
  have hint : Integrable (fun v : Fin 2 → ℝ => f (chartGL v * (wPerm * x))) :=
    integrable_chart (RealStrictCharacterLanglandsQuotient.isSignedPower _)
      (isStrictlyDominant (e := e) hs hℓ) hf hκ
  have hmp := (volume_preserving_finTwoArrow ℝ).symm
  have hint2 : Integrable (fun z : ℝ × ℝ =>
      f (chartGL ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm z) * (wPerm * x)))
      ((volume : Measure ℝ).prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hint
  unfold chartIntegral
  rw [← hmp.integral_comp' (fun v : Fin 2 → ℝ => f (chartGL v * (wPerm * x))),
    Measure.volume_eq_prod ℝ ℝ, integral_prod _ hint2]
  have e1 : ∀ a b : ℝ, f (chartGL ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm (a, b)) *
      (wPerm * x)) = f (nbar1 b * s1 * (nbar0 a * s0 * x)) := by
    intro a b
    rw [← mul_assoc, chartGL_mul_wPerm]
    simp only [mul_assoc]
    rfl
  simp_rw [e1, integral_nbar1 hs hf]
  exact integral_eq_kernelOp 0 (n + d.weight.natAbs) nbar0 s0 _ (kernelOp_nbar0_cotan hs hf) x

/-- **Integrability for the landing.** For `κ ∈ O(3)`, the function
`(θ, w) ↦ f(r_0(θ) chartGL w κ) e^{-ikθ}` is integrable on `(0, 2π] × ℝ²`. -/
theorem integrable_landing
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ principalSeries ℝ 3 (posChar d e s)) (hℓ : 0 < d.weight.natAbs)
    {κ : Langlands.GeneralLinear 3 ℝ} (hκ : κ ∈ unitaryCompact ℝ 3) (k : ℤ) :
    Integrable (Function.uncurry fun (θ : ℝ) (w : Fin 2 → ℝ) =>
        f (blockRotation 3 0 θ * (chartGL w * κ)) *
          Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I)))
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) := by
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hfc : Continuous f := continuous_of_mem_principalSeries hf
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hfc
  set G : ℝ × (Fin 2 → ℝ) → ℂ := fun p =>
    f (chartGL p.2 * (blockRotation 3 0 p.1 * κ)) *
      Complex.exp (-((k : ℂ) * (p.1 : ℂ) * Complex.I)) with hG
  have hGc : Continuous G := by
    refine (hfc.comp ((continuous_chartGL.comp continuous_snd).mul
      (((continuous_blockRotation 3 0).comp continuous_fst).mul continuous_const))).mul ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  have hbound : Integrable (fun p : ℝ × (Fin 2 → ℝ) => C * ∏ l : Fin 2, (1 + p.2 l ^ 2) ^
      chartExponent
        (realPositionExponent [RealBlock.induced d, RealBlock.character (charData e s)]) l)
      ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) :=
    ((ParabolicChartBound.integrable_prod_one_add_sq_rpow
      (chartExponent_lt (isStrictlyDominant (e := e) hs hℓ))).const_mul C).comp_snd _
  have hGint : Integrable G ((volume.restrict (Set.Ioc 0 (2 * Real.pi))).prod volume) := by
    refine Integrable.mono' hbound hGc.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have hκ' : blockRotation 3 0 p.1 * κ ∈ unitaryCompact ℝ 3 :=
      Subgroup.mul_mem _ (blockRotation_mem_unitaryCompact 3 0 p.1) hκ
    simp only [hG, norm_mul]
    rw [norm_exp_neg_mul_I, mul_one]
    exact norm_le_of_mem_principalSeries (RealStrictCharacterLanglandsQuotient.isSignedPower _)
      (isStrictlyDominant (e := e) hs hℓ) hf hC p.2 hκ'
  have hmeas : Measurable (Function.uncurry fun (θ : ℝ) (w : Fin 2 → ℝ) => w ᵥ* rotInv θ) :=
    (continuous_snd.matrix_vecMul (continuous_rotInv.comp continuous_fst)).measurable
  have hmap : ∀ θ : ℝ, Measure.map (fun w : Fin 2 → ℝ => w ᵥ* rotInv θ) volume = volume := by
    intro θ
    have hB : (rotInv θ).det ≠ 0 := by
      rw [det_rotInv]
      exact one_ne_zero
    have hfun : (⇑(vecMulEquiv hB) : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = fun w => w ᵥ* rotInv θ :=
      funext (vecMulEquiv_apply hB)
    have h := map_vecMulEquiv hB
    rw [hfun, det_rotInv, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
    exact h
  have hskew := MeasurePreserving.skew_product
    (MeasurePreserving.id (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) hmeas (ae_of_all _ hmap)
  refine (hskew.integrable_comp_of_integrable hGint).congr (ae_of_all _ fun p => ?_)
  simp only [Function.comp, Function.uncurry, hG, id]
  rw [← mul_assoc, ← rot0_mul_chartGL, mul_assoc]

/-- **The landing of the chart integral.** For `x ∈ O(3)` and `|k| < ℓ`, the Fourier coefficient
`Φ¹_k` of the chart integral vanishes at `x`. -/
theorem blockFourierCoefficient_chartIntegral
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ realStandardModule 3 [RealBlock.induced d, RealBlock.character (charData e s)])
    (hℓ : 0 < d.weight.natAbs) {g : Langlands.GeneralLinear 3 ℝ}
    (hg : g ∈ unitaryCompact ℝ 3) {k : ℤ} (hk : |k| < |d.weight|) :
    blockFourierCoefficient 3 1 k (chartIntegral f) g = 0 := by
  have hκ : wPerm * g ∈ unitaryCompact ℝ 3 :=
    Subgroup.mul_mem _ wPerm_mem_unitaryCompact hg
  have hrot : ∀ θ : ℝ, chartIntegral f (blockRotation 3 1 θ * g) =
      ∫ w : Fin 2 → ℝ, f (blockRotation 3 0 θ * (chartGL w * (wPerm * g))) := by
    intro θ
    unfold chartIntegral
    have e1 : wPerm * (blockRotation 3 1 θ * g) = blockRotation 3 0 θ * (wPerm * g) := by
      rw [← mul_assoc, wPerm_mul_rot1, mul_assoc]
    rw [e1]
    have hB : (rotInv θ).det ≠ 0 := by
      rw [det_rotInv]
      exact one_ne_zero
    have h2 := integral_vecMul_eq hB
      (fun v : Fin 2 → ℝ => f (chartGL v * (blockRotation 3 0 θ * (wPerm * g))))
    rw [det_rotInv, abs_one, inv_one, Complex.ofReal_one, one_mul] at h2
    rw [← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only
    rw [← mul_assoc, ← rot0_mul_chartGL, mul_assoc]
  unfold blockFourierCoefficient
  simp_rw [hrot, ← integral_mul_const]
  rw [intervalIntegral_integral_swap (integrable_landing hs hf.1 hℓ hκ k)]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)).trans
    (integral_zero (Fin 2 → ℝ) ℂ)
  exact hf.2 0 d rfl k hk _

/-- **The landing.** For `x ∈ O(3)` and `|k| < ℓ`, `Φ¹_k (C⁰_{n+ℓ} C¹_n f)(x) = 0`. -/
theorem landing
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ realStandardModule 3 [RealBlock.induced d, RealBlock.character (charData e s)])
    (hℓ : 0 < d.weight.natAbs) {g : Langlands.GeneralLinear 3 ℝ}
    (hg : g ∈ unitaryCompact ℝ 3) {k : ℤ} (hk : |k| < |d.weight|) :
    blockFourierCoefficient 3 1 k (kernelOp 3 0 (n + d.weight.natAbs) (kernelOp 3 1 n f)) g =
      0 := by
  have huI : ∀ x ∈ unitaryCompact ℝ 3,
      kernelOp 3 0 (n + d.weight.natAbs) (kernelOp 3 1 n f) x =
        (-1 : ℂ) ^ (d.weight.natAbs + 1) * chartIntegral f x := by
    intro x hx
    rw [chartIntegral_eq hs hf.1 hℓ hx, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_mul]
  rw [RealSwapFLanding.blockFourierCoefficient_congr huI 1 k hg]
  have h0 := blockFourierCoefficient_chartIntegral hs hf hℓ hg hk
  unfold blockFourierCoefficient at h0 ⊢
  simp_rw [mul_assoc ((-1 : ℂ) ^ (d.weight.natAbs + 1))]
  rw [intervalIntegral.integral_const_mul, h0, mul_zero]

end Landing

/-! ## The special landing -/

/-- **`SpecialLanding` holds.** -/
theorem specialLanding : RealSwapLandingAlgebra.SpecialLanding := by
  intro c d f hf n
  obtain ⟨f', hf', hval⟩ :=
    exists_extension c d (d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1)) hf
  have hf'c : Continuous f' := continuous_of_mem_principalSeries hf'.1.1
  have hp1 : 1 + 1 < 3 := by norm_num
  have hp0 : 0 + 1 < 3 := by norm_num
  refine ⟨sinKernel (n + d.weight.natAbs), sinKernel n, kernelOp 3 1 n f',
    kernelOp 3 0 (n + d.weight.natAbs) (kernelOp 3 1 n f'), isRecurrent_sinKernel n _,
    isSymmetric_sinKernel n _, sinKernel_zero_ne_zero n, sinKernel_one_ne_zero n, ?_,
    isSymmetric_sinKernel _ _, sinKernel_zero_ne_zero _, sinKernel_one_ne_zero _,
    continuous_kernelOp 1 n hf'c, continuous_kernelOp 0 _ (continuous_kernelOp 1 n hf'c),
    ?_, ?_, ?_⟩
  · have e : (((n + d.weight.natAbs : ℕ) : ℂ) + 2) = (n : ℂ) + 2 + (d.weight.natAbs : ℂ) := by
      push_cast
      ring
    have := isRecurrent_sinKernel (n + d.weight.natAbs)
      ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
    rwa [e] at this
  · intro g hg k
    rw [blockFourierCoefficient_kernelOp hp1 n hf'c k g,
      RealSwapFLanding.blockFourierCoefficient_congr hval 1 k hg]
  · intro g _ k
    exact blockFourierCoefficient_kernelOp hp0 _ (continuous_kernelOp 1 n hf'c) k g
  · intro g hg k hk
    rcases Nat.eq_zero_or_pos d.weight.natAbs with h0 | hℓ
    · exfalso
      have h : |d.weight| = 0 := by
        rw [Int.abs_eq_natAbs, h0]
        rfl
      rw [h] at hk
      exact absurd hk (not_lt.mpr (abs_nonneg k))
    · exact landing (n := n) rfl hf'.1 hℓ hg hk

/-- **The induced-first landing.** `RealSwapLandingInducedFirstStatement` holds. -/
theorem inducedFirst : RealSwapLandingInducedFirstStatement :=
  RealSwapLandingAlgebra.inducedFirst_of_special specialLanding

end RealSwapLandingIntegral

end Langlands.Archimedean
