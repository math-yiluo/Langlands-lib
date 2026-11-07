import Langlands.Global.HeckeCharacter
import Langlands.Global.CompletionPadic
import Langlands.Global.CompletionResidue
import Langlands.Global.NormOneIdeleClassCompact
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.LocalFactor.Abelian.Padic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Absolute convergence of Hecke Euler products

For a Hecke character `χ` of a number field `K`, the finite rank-one local factors
`LocalFactor.PadicAbelian.lFactor (CompletionPadic.topologicalData v) (χ.finiteComponent v) s`
form an absolutely convergent Euler product on a right half-plane, over every set of
finite places, and the value of the product is nonzero. See the paired Markdown.
-/

noncomputable section

universe u

namespace Langlands.Global.HeckeEulerProduct

open NumberField IsDedekindDomain Filter Topology
open Langlands.Global.CompletionPadic
open scoped NNReal WithZero Valued

variable {K : Type u} [Field K] [NumberField K]

section Local

/-- The valuation integers of `topologicalData v` are the closed unit ball of the completion. -/
theorem mem_integers_iff (v : FinitePlace K) (x : FiniteCompletion K v) :
    x ∈ (topologicalData v).Integers ↔ ‖x‖ ≤ 1 := by
  let := (topologicalData v).valuativeRel
  have he := AdelicFunctoriality.valuativeRel_valuation_isEquiv (topologicalData v) Valued.v
    (topologicalData_vle v)
  change ValuativeRel.valuation (v.adicCompletion K) x ≤ 1 ↔ _
  rw [he.le_one_iff_le_one, NumberField.FinitePlace.norm_def, NNReal.coe_le_one]
  exact (WithZeroMulInt.toNNReal_le_one_iff
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).symm

/-- The valuation integers of `topologicalData v` and the norm integers of the completion. -/
def integersEquiv (v : FinitePlace K) :
    (topologicalData v).Integers ≃+* LocalGalois.baseIntegers (FiniteCompletion K v) where
  toFun x := ⟨x.1, by
    change ‖x.1‖₊ ≤ 1
    exact_mod_cast (mem_integers_iff v x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_integers_iff v x.1).mpr (by
    have : ‖x.1‖₊ ≤ 1 := x.2
    exact_mod_cast this)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The residue cardinality of `topologicalData v` is the absolute norm of `v`. -/
theorem residueCardinality_eq (v : FinitePlace K) :
    (topologicalData v).residueCardinality = Ideal.absNorm v.asIdeal := by
  rw [PadicField.TopologicalData.residueCardinality,
    ← CompletionResidue.card_residueField K v]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (integersEquiv v)).toEquiv

/-- The uniformizer of `topologicalData v` has norm `N(v)⁻¹` in the completion. -/
theorem norm_uniformizerUnit (v : FinitePlace K) :
    ‖((LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v) :
        (FiniteCompletion K v)ˣ) : FiniteCompletion K v)‖ =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hv : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      ((LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v) :
        (FiniteCompletion K v)ˣ) : FiniteCompletion K v) = WithZero.exp (-1) := by
    rw [← AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation v]
    simpa using LocalFactor.PadicAbelian.uniformizerUnit_zpow_value (topologicalData v) 1
  rw [FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  have h1 : (WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ)))).toAdd = -1 := rfl
  rw [h1]
  simp

end Local

section Summable

/-- The partial sums of the ideal-counting coefficients are `O(n)`. -/
theorem sum_card_absNorm_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have htend : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
      fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ _ htend
  filter_upwards [eventually_ne_atTop 0] with n hn h
  exact absurd h (by exact_mod_cast hn)

/-- `∑_𝔭 N(𝔭)^(-σ)` converges for `σ > 1`, the sum running over the finite places. -/
theorem summable_absNorm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : FinitePlace K ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) := by
  classical
  have hL : LSeriesSummable
      (fun n ↦ ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) σ :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg sum_card_absNorm_isBigO
      (fun _ ↦ Nat.cast_nonneg _) zero_le_one (by simpa using hσ)
  have hterm : Summable (fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) *
        (if n = 0 then 0 else (n : ℝ) ^ (-σ))) := by
    refine hL.norm.congr fun n ↦ ?_
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  let F : Ideal (𝓞 K) → ℝ := fun I ↦
    if Ideal.absNorm I = 0 then 0 else (Ideal.absNorm I : ℝ) ^ (-σ)
  have hF : Summable F := by
    rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ by
      simp only [Function.comp_apply, F]; split_ifs <;> positivity)).mpr ⟨fun n ↦ ?_, ?_⟩
    · have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      exact Summable.of_finite
    · refine hterm.congr fun n ↦ ?_
      have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
      have hc : ∀ y : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
          (F ∘ Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)) ⟨n, y⟩ =
            if n = 0 then 0 else (n : ℝ) ^ (-σ) := by
        intro y
        simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, F, y.2]
      simp_rw [hc, tsum_const, nsmul_eq_mul]
  have hinj : Function.Injective (fun v : FinitePlace K ↦ v.asIdeal) :=
    fun a b h ↦ HeightOneSpectrum.ext h
  refine (hF.comp_injective hinj).congr fun v ↦ ?_
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  simp [F, hne]

end Summable

section Exponent

/-- A Hecke character has absolute value one on the idele classes of norm one. -/
theorem norm_eq_one_of_ideleClass_eq_one (χ : HeckeCharacter K) {c : IdeleClasses K}
    (hc : IdeleAbsoluteValue.ideleClass K c = 1) : ‖(χ c : ℂ)‖ = 1 := by
  set H := (IdeleAbsoluteValue.ideleClass K).toMonoidHom.ker
  have hcont : Continuous fun d : IdeleClasses K ↦ (χ d : ℂ) :=
    Units.continuous_val.comp (map_continuous χ)
  obtain ⟨M, hM⟩ :=
    (NormOneIdeleClass.isCompact_ker_ideleClass K).exists_bound_of_continuousOn
      hcont.continuousOn
  have key : ∀ d ∈ H, ‖(χ d : ℂ)‖ ≤ 1 := by
    intro d hd
    by_contra! h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have hdn := hM (d ^ n) (pow_mem hd n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at hdn
    exact absurd hdn (not_le.mpr hn)
  have hmem : c ∈ H := hc
  have h1 := key c hmem
  have h2 := key c⁻¹ (inv_mem hmem)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖(χ c : ℂ)‖ := norm_pos_iff.mpr (χ c).ne_zero
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

omit [NumberField K] in
/-- Every archimedean completion receives a norm-preserving ring map from `ℝ`. -/
theorem exists_norm_ringHom (w : InfinitePlace K) :
    ∃ r : ℝ →+* InfiniteCompletion K w, ∀ x, ‖r x‖ = ‖x‖ := by
  by_cases hw : w.IsReal
  · refine ⟨(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom, fun x ↦ ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x)
    change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x‖ = ‖x‖
    rw [← h]
    exact congrArg norm ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply x)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine ⟨(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toRingHom.comp
      Complex.ofRealHom, fun x ↦ ?_⟩
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ))
    change ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ)‖ = ‖x‖
    rw [← h]
    refine (congrArg norm
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).apply_symm_apply (x : ℂ))).trans ?_
    simp

/-- The positive real ray `t ↦ r(exp t)` in the units of an archimedean completion. -/
def ray {w : InfinitePlace K} (r : ℝ →+* InfiniteCompletion K w) (t : ℝ) :
    (InfiniteCompletion K w)ˣ :=
  Units.map r.toMonoidHom (Units.mk0 (Real.exp t) (Real.exp_pos t).ne')

omit [NumberField K] in
theorem coe_ray {w : InfinitePlace K} (r : ℝ →+* InfiniteCompletion K w) (t : ℝ) :
    ((ray r t : (InfiniteCompletion K w)ˣ) : InfiniteCompletion K w) = r (Real.exp t) := rfl

omit [NumberField K] in
theorem ray_add {w : InfinitePlace K} (r : ℝ →+* InfiniteCompletion K w) (s t : ℝ) :
    ray r (s + t) = ray r s * ray r t := by
  ext
  simp [coe_ray, Real.exp_add]

omit [NumberField K] in
theorem continuous_ray {w : InfinitePlace K} (r : ℝ →+* InfiniteCompletion K w)
    (hr : ∀ x, ‖r x‖ = ‖x‖) : Continuous (ray r) := by
  have hrc : Continuous r := (AddMonoidHomClass.isometry_of_norm r hr).continuous
  refine Units.continuous_iff.mpr ⟨hrc.comp Real.continuous_exp, ?_⟩
  have : (fun t ↦ (((ray r t)⁻¹ : (InfiniteCompletion K w)ˣ) : InfiniteCompletion K w)) =
      fun t ↦ r (Real.exp (-t)) := by
    funext t
    rw [Units.val_inv_eq_inv_val, coe_ray, ← map_inv₀, Real.exp_neg]
  rw [this]
  exact hrc.comp (Real.continuous_exp.comp continuous_neg)

omit [NumberField K] in
theorem norm_ray {w : InfinitePlace K} (r : ℝ →+* InfiniteCompletion K w)
    (hr : ∀ x, ‖r x‖ = ‖x‖) (t : ℝ) :
    ‖((ray r t : (InfiniteCompletion K w)ˣ) : InfiniteCompletion K w)‖ = Real.exp t := by
  rw [coe_ray, hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

/-- Along the positive real ray, `‖χ_w‖` is an exponential `exp (β t)`. -/
theorem exists_norm_infiniteComponent_ray (χ : HeckeCharacter K) {w : InfinitePlace K}
    (r : ℝ →+* InfiniteCompletion K w) (hr : ∀ x, ‖r x‖ = ‖x‖) :
    ∃ β : ℝ, ∀ t : ℝ, ‖(χ.infiniteComponent w (ray r t) : ℂ)‖ = Real.exp (β * t) := by
  let h : ℝ → ℝ := fun t ↦ Real.log ‖(χ.infiniteComponent w (ray r t) : ℂ)‖
  have hne : ∀ t, ‖(χ.infiniteComponent w (ray r t) : ℂ)‖ ≠ 0 := fun t ↦
    norm_ne_zero_iff.mpr (χ.infiniteComponent w (ray r t)).ne_zero
  have hadd : ∀ s t, h (s + t) = h s + h t := by
    intro s t
    simp only [h, ray_add, map_mul, Units.val_mul, norm_mul]
    exact Real.log_mul (hne s) (hne t)
  have hcont : Continuous h := by
    refine Continuous.log ?_ hne
    exact continuous_norm.comp (Units.continuous_val.comp
      ((map_continuous (χ.infiniteComponent w)).comp (continuous_ray r hr)))
  let f : ℝ →+ ℝ := AddMonoidHom.mk' h hadd
  refine ⟨h 1, fun t ↦ ?_⟩
  have hlin : h t = t * h 1 := by
    have := map_real_smul f hcont t 1
    simpa [f] using this
  rw [mul_comm, ← hlin, Real.exp_log (norm_pos_iff.mpr (χ.infiniteComponent w (ray r t)).ne_zero)]

/-- There is one real exponent `β` with `‖χ_v(ϖ_v)‖ = N(v)^(-β)` at every finite place `v`. -/
theorem exists_norm_finiteComponent_uniformizer (χ : HeckeCharacter K) :
    ∃ β : ℝ, ∀ v : FinitePlace K,
      ‖((χ.finiteComponent v (LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v)) :
          ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-β) := by
  let w : InfinitePlace K := Classical.arbitrary _
  obtain ⟨r, hr⟩ := exists_norm_ringHom w
  obtain ⟨β₀, hβ₀⟩ := exists_norm_infiniteComponent_ray χ r hr
  have hm : (0 : ℝ) < w.mult := by exact_mod_cast InfinitePlace.mult_pos
  refine ⟨β₀ / w.mult, fun v ↦ ?_⟩
  set ϖ := LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v)
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (zero_lt_one.trans this)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set t : ℝ := Real.log N / w.mult
  have hmt : (w.mult : ℝ) * t = Real.log N := by
    simp only [t]
    field_simp
  let c := finiteClassInclusion K v ϖ * infiniteClassInclusion K w (ray r t)
  have hc : IdeleAbsoluteValue.ideleClass K c = 1 := by
    apply Units.ext
    apply NNReal.eq
    rw [Units.val_one, NNReal.coe_one, map_mul, Units.val_mul, NNReal.coe_mul,
      IdeleAbsoluteValue.coe_ideleClass_finiteClassInclusion,
      IdeleAbsoluteValue.coe_ideleClass_infiniteClassInclusion, norm_uniformizerUnit,
      norm_ray r hr, ← Real.exp_nat_mul, hmt, Real.exp_log hN]
    exact inv_mul_cancel₀ hN.ne'
  have h1 := norm_eq_one_of_ideleClass_eq_one χ hc
  rw [map_mul, Units.val_mul, norm_mul] at h1
  have h2 : ‖(χ (infiniteClassInclusion K w (ray r t)) : ℂ)‖ = Real.exp (β₀ * t) := hβ₀ t
  rw [h2] at h1
  change ‖(χ (finiteClassInclusion K v ϖ) : ℂ)‖ = _
  rw [eq_inv_of_mul_eq_one_left h1, ← Real.exp_neg, Real.rpow_def_of_pos hN]
  congr 1
  simp only [t]
  field_simp

end Exponent

section EulerProduct

open LocalFactor.PadicAbelian in
/-- The Euler-factor coefficient: `χ_v(ϖ_v) q_v^{-s}` when `χ_v` is unramified, else `0`. -/
def coeff (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) : ℂ :=
  if (topologicalData v).multiplicativeConductor (χ.finiteComponent v) = 0 then
    (χ.finiteComponent v (uniformizerUnit (topologicalData v)) : ℂ) *
      spectralVariable (topologicalData v) s
  else 0

theorem lFactor_eq (χ : HeckeCharacter K) (v : FinitePlace K) (s : ℂ) :
    LocalFactor.PadicAbelian.lFactor (topologicalData v) (χ.finiteComponent v) s =
      (1 - coeff χ v s)⁻¹ := by
  unfold LocalFactor.PadicAbelian.lFactor LocalFactor.PadicAbelian.lFactorAt coeff
  split_ifs
  · rfl
  · simp

theorem norm_spectralVariable (v : FinitePlace K) (s : ℂ) :
    ‖LocalFactor.PadicAbelian.spectralVariable (topologicalData v) s‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (zero_lt_one.trans this)
  rw [LocalFactor.PadicAbelian.spectralVariable, Complex.norm_exp, residueCardinality_eq,
    Real.rpow_def_of_pos hN]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

theorem norm_coeff_le (χ : HeckeCharacter K) {β : ℝ}
    (hβ : ∀ v : FinitePlace K,
      ‖((χ.finiteComponent v (LocalFactor.PadicAbelian.uniformizerUnit (topologicalData v)) :
          ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-β))
    (v : FinitePlace K) (s : ℂ) :
    ‖coeff χ v s‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(β + s.re)) := by
  have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (zero_lt_one.trans this)
  unfold coeff
  split_ifs
  · rw [norm_mul, hβ, norm_spectralVariable, ← Real.rpow_add hN, neg_add]
  · rw [norm_zero]
    positivity

/-- An absolutely convergent product of inverse factors `(1 - a i)⁻¹` has a nonzero value. -/
theorem exists_hasProd_inv_one_sub {ι : Type*} (a : ι → ℂ) (ha : Summable fun i ↦ ‖a i‖)
    (h1 : ∀ i, ‖a i‖ < 1) : ∃ L : ℂ, L ≠ 0 ∧ HasProd (fun i ↦ (1 - a i)⁻¹) L := by
  have hs : Summable fun i ↦ ‖-a i‖ := by simpa using ha
  have hne : ∀ i, 1 + -a i ≠ 0 := by
    intro i h
    have : a i = 1 := by linear_combination -h
    have := h1 i
    simp_all
  have hP := tprod_one_add_ne_zero_of_summable hne hs
  refine ⟨(∏' i, (1 + -a i))⁻¹, inv_ne_zero hP, ?_⟩
  simpa [← sub_eq_add_neg] using (multipliable_one_add_of_summable hs).hasProd.inv₀ hP

/-- The finite Euler product of a Hecke character, over any set `S` of finite places,
converges on a right half-plane independent of `S`, to a nonzero value. -/
theorem exists_hasProd_lFactor_subtype (χ : HeckeCharacter K) :
    ∃ σ₀ : ℝ, ∀ (S : Set (FinitePlace K)) (s : ℂ), σ₀ < s.re →
      ∃ L : ℂ, L ≠ 0 ∧ HasProd (fun v : S ↦
        LocalFactor.PadicAbelian.lFactor (topologicalData v.1) (χ.finiteComponent v.1) s) L := by
  obtain ⟨β, hβ⟩ := exists_norm_finiteComponent_uniformizer χ
  refine ⟨1 - β, fun S s hs ↦ ?_⟩
  have hσ : 1 < β + s.re := by linarith
  have hsum : Summable fun v : FinitePlace K ↦ ‖coeff χ v s‖ :=
    (summable_absNorm_rpow hσ).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun v ↦ norm_coeff_le χ hβ v s)
  have hlt : ∀ v : FinitePlace K, ‖coeff χ v s‖ < 1 := by
    intro v
    refine (norm_coeff_le χ hβ v s).trans_lt (Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith))
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨L, hL, hprod⟩ := exists_hasProd_inv_one_sub (fun v : S ↦ coeff χ v.1 s)
    (hsum.subtype S) (fun v ↦ hlt v.1)
  exact ⟨L, hL, by simpa only [lFactor_eq] using hprod⟩

/-- The finite Euler product of a Hecke character over all finite places converges on a right
half-plane to a nonzero value. -/
theorem exists_hasProd_lFactor (χ : HeckeCharacter K) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      ∃ L : ℂ, L ≠ 0 ∧ HasProd (fun v : FinitePlace K ↦
        LocalFactor.PadicAbelian.lFactor (topologicalData v) (χ.finiteComponent v) s) L := by
  obtain ⟨σ₀, h⟩ := exists_hasProd_lFactor_subtype χ
  refine ⟨σ₀, fun s hs ↦ ?_⟩
  obtain ⟨L, hL, hprod⟩ := h Set.univ s hs
  exact ⟨L, hL, (Equiv.Set.univ (FinitePlace K)).hasProd_iff.mp hprod⟩

end EulerProduct

end Langlands.Global.HeckeEulerProduct
