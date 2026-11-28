import Langlands.Global.AdelicWeakConstantTermLeviEstimates
import Langlands.Global.AdelicNormOneSiegelDominatedIntegrability
import Langlands.Global.AdelicInducedInnerProductIntegrable

/-! # The Levi Schwartz estimate for `A^2_P` from Siegel-set decay

Delorme 2023, §3.4 (`A^2(G) ⊂ C(G)`, from Mœglin–Waldspurger I.4.1 and I.4.11), applied to the
Levi subgroup `M = M_J`, in the form used by the Library: a pointwise bound on Siegel sets of
`M` instead of Delorme's function `Ξ^{[M]}` and (2.10).

* `SquareIntegrableInducedFormSiegelDecayStatement`: every `φ ∈ A^2_P` satisfies
  `|φ(x k)| ≤ B_n δ(a)^{1/2} σ_M(x)^{-n}` for every `n`, uniformly in `k ∈ K`, at the norm-one
  points `x` of every Siegel set of `M`, where `a` is the torus coordinate of `x`.

The theorem `squareIntegrableInducedFormLeviSchwartz_of_siegelDecay` derives
`SquareIntegrableInducedFormLeviSchwartzStatement` from it and the proved
`normOneSiegelDecayIntegrability`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  AdelicSiegelFactors

/-- **Siegel-set decay of square-integrable inducing forms on the Levi** (Delorme 2023, §3.4:
`A^2(G) ⊂ C(G)` by Mœglin–Waldspurger I.4.1 and I.4.11, applied to the Levi subgroup `M` of
`P = P_J` and the normalized slices `m ↦ δ_P(m)^{-1/2} φ(m k)` of Mœglin–Waldspurger I.2.17,
split by central characters as in I.3.2; on `M(𝔸)^1` these slices equal `m ↦ φ(m k)`).
Take the hypotheses of `SquareIntegrableInducedFormLeviSchwartzStatement`: a number
field `F`, a connected reductive `G`, a maximal compact `K ⊆ G(𝔸)` with `P_∅(𝔸) K = G(𝔸)` for
a compatible family `𝓕` of standard parabolics, a closed matrix embedding `rho`, a standard
index `J` and `φ ∈ A^2_P` for `K` (`IsSquareIntegrableInducedForm`). Then for every algebraic
Siegel setup `(T, i, ν, T₀, j)` of `M = 𝓕.M J`, compact factors `C` (whose compact subgroup is
arbitrary), threshold `t`, compact `Ω ⊆ M(𝔸)` and `n : ℕ` there is `B` with

`‖φ(x k)‖ ≤ B δ(a)^{1/2} / σ_M(x)^n`

for every norm-one point `x ∈ M(𝔸)^1` of the Siegel set `A_M · Ω_N Ω_M A_{T₀}(t) K_C · Ω` of
`M` with torus coordinate `a` and every `k ∈ K`. Here `x k` is computed in `G(𝔸)` through
`M → P → G`, `δ = siegelModulus` is the modulus of the minimal parabolic of the setup and
`σ_M = adelicLogHeight` is the logarithmic height of `M` for `rho` restricted along `M → P → G`. -/
def SquareIntegrableInducedFormSiegelDecayStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (𝓕 : StandardParabolicFamily F G) (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
      (J : StandardIndex F G 𝓕.i 𝓕.ν) (φ : AdelicGroupPoints F G → ℂ),
    IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc
      (𝓕.p J) (𝓕.iU J) (𝓕.l J) φ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ 𝓕.M J)
      (ν : cocharacterLattice T) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ T), IsSiegelAlgebraicSetup F (𝓕.M J) T i ν T₀ j →
    ∀ (C : CompactFactors F (𝓕.M J) (Standard.unipotentScheme i ν ∅)
        (Standard.leviScheme i ν ∅))
      (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F (𝓕.M J))), IsCompact Ω →
    ∀ n : ℕ, ∃ B : ℝ, ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
      (x : AdelicGroupPoints F (𝓕.M J)),
      IsSiegelPoint F (𝓕.M J) T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F (𝓕.M J) →
      ∀ k ∈ K,
        ‖φ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) x * k)‖ ≤
          B * Real.sqrt (siegelModulus F (𝓕.M J) T i ν T₀ j a) /
            adelicLogHeight F (𝓕.M J) (rho.restrict (𝓕.l J ≫ 𝓕.p J)) x ^ n

/-- **Reduction.** `SquareIntegrableInducedFormSiegelDecayStatement` implies
`SquareIntegrableInducedFormLeviSchwartzStatement`. -/
theorem squareIntegrableInducedFormLeviSchwartz_of_siegelDecay
    (hdecay : SquareIntegrableInducedFormSiegelDecayStatement) :
    SquareIntegrableInducedFormLeviSchwartzStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho 𝓕 hK J φ hφ n
  let incl := map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)
  let ρM := rho.restrict (𝓕.l J ≫ 𝓕.p J)
  have hM : IsConnectedReductive (𝓕.M J) := (𝓕.isCompatible J).levi.isConnectedReductive
  have hρM : IsClosedSubgroup ρM :=
    ((𝓕.isCompatible J).levi.isClosedSubgroup.comp
      (𝓕.isCompatible J).parabolic.isClosedSubgroup).comp hrho
  obtain ⟨T, i, ν, T₀, j, hset, C, t, Ω, e, hΩ, hint⟩ :=
    normOneSiegelDecayIntegrability F (𝓕.M J) hM ρM hρM
  obtain ⟨B, hB⟩ :=
    hdecay F G hred K rho hsmooth hcalc hKmax hrho 𝓕 hK J φ hφ T i ν T₀ j hset C t Ω hΩ (n + e)
  -- properties of `φ`
  have hcont : Continuous φ := hφ.1.2.1.1
  have hinvφ : ∀ q ∈ rationalSubgroup F (𝓕.M J), ∀ g : AdelicGroupPoints F G,
      φ (incl q * g) = φ g := by
    intro q hq g
    change φ (map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J) q * g) = φ g
    rw [InducedInnerProductIntegrable.map_comp_apply]
    exact hφ.1.1 _ (InducedInnerProductIntegrable.map_map_mem_parabolicQuotientSubgroup
      (𝓕.p J) (𝓕.iU J) (𝓕.l J) hq) g
  -- notation for the measures and the weight
  let μK := compactHaarProbability F G K hK.isCompact
  let μ₁ := normOneRationalQuotientHaarMeasure F (𝓕.M J)
  have : IsFiniteMeasure μ₁ :=
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F (𝓕.M J) hM
  let σ : AdelicGroupPoints F (𝓕.M J) → ℝ := fun x =>
    rationalLogHeight F (𝓕.M J) ρM (LeftCosetSpace.mk (rationalSubgroup F (𝓕.M J)) x)
  have hσmeas : Measurable σ :=
    (measurable_rationalLogHeight ρM).comp (LeftCosetSpace.measurable_mk _)
  have hσ1 : ∀ x, 1 ≤ σ x := fun x => one_le_rationalLogHeight ρM _
  have hσinv : ∀ q ∈ rationalSubgroup F (𝓕.M J), ∀ x, σ (q * x) = σ x := by
    intro q hq x
    change rationalLogHeight F (𝓕.M J) ρM (LeftCosetSpace.mk _ (q * x)) =
      rationalLogHeight F (𝓕.M J) ρM (LeftCosetSpace.mk _ x)
    rw [LeftCosetSpace.mk_subgroup_mul (rationalSubgroup F (𝓕.M J)) ⟨q, hq⟩ x]
  have hσout : ∀ y : NormOneRationalQuotient F (𝓕.M J),
      rationalLogHeight F (𝓕.M J) ρM (normOneQuotientInclusion F (𝓕.M J) y) =
        σ ((Quotient.out y : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) := by
    intro y
    conv_lhs => rw [← Quotient.out_eq y]
    rfl
  -- the target function and its measurability
  set g : K × NormOneRationalQuotient F (𝓕.M J) → ℂ := fun z =>
    φ (incl ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G)) *
      ((rationalLogHeight F (𝓕.M J) ρM (normOneQuotientInclusion F (𝓕.M J) z.2) : ℝ) : ℂ) ^ n
    with hgdef
  have hφpart : Continuous (fun z : K × NormOneRationalQuotient F (𝓕.M J) =>
      φ (incl ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) *
        (z.1 : AdelicGroupPoints F G))) := by
    refine LeftCosetSpace.continuous_out_of_invariant (rationalNormOneSubgroup F (𝓕.M J))
      (fun (k : K) (m : normOneSubgroup F (𝓕.M J)) =>
        φ (incl (m : AdelicGroupPoints F (𝓕.M J)) * (k : AdelicGroupPoints F G))) ?_ ?_
    · exact hcont.comp ((incl.continuous.comp (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst))
    · intro k r hr m
      have hr' : (r : AdelicGroupPoints F (𝓕.M J)) ∈ rationalSubgroup F (𝓕.M J) := by
        obtain ⟨q, hq⟩ := hr
        exact ⟨q, congrArg Subtype.val hq⟩
      change φ (incl ((r : AdelicGroupPoints F (𝓕.M J)) * m) * (k : AdelicGroupPoints F G)) =
        φ (incl (m : AdelicGroupPoints F (𝓕.M J)) * (k : AdelicGroupPoints F G))
      rw [map_mul, mul_assoc, hinvφ _ hr']
  have hσpart : Measurable (fun z : K × NormOneRationalQuotient F (𝓕.M J) =>
      ((rationalLogHeight F (𝓕.M J) ρM (normOneQuotientInclusion F (𝓕.M J) z.2) : ℝ) : ℂ) ^ n) :=
    ((Complex.measurable_ofReal.comp ((measurable_rationalLogHeight ρM).comp
      ((continuous_normOneQuotientInclusion F (𝓕.M J)).measurable.comp measurable_snd))).pow_const n)
  have hmeas : AEStronglyMeasurable g (μK.prod μ₁) :=
    hφpart.aestronglyMeasurable.mul hσpart.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ⟨hmeas.norm.pow 2, ?_⟩
  -- the dominated invariant function on `M(𝔸)`
  let h₀ : AdelicGroupPoints F (𝓕.M J) × K → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((‖φ (incl p.1 * (p.2 : AdelicGroupPoints F G))‖ * σ p.1 ^ n) ^ 2 / (B ^ 2 + 1))
  have hh₀meas : Measurable h₀ :=
    ENNReal.measurable_ofReal.comp
      ((((hcont.comp ((incl.continuous.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))).measurable.norm.mul
          ((hσmeas.comp measurable_fst).pow_const n)).pow_const 2).div_const _)
  set f : AdelicGroupPoints F (𝓕.M J) → ℝ≥0∞ := fun x => ∫⁻ k, h₀ (x, k) ∂μK with hfdef
  have hfmeas : Measurable f := hh₀meas.lintegral_prod_right'
  have hfinv : ∀ q ∈ rationalSubgroup F (𝓕.M J), ∀ x : AdelicGroupPoints F (𝓕.M J),
      f (q * x) = f x := by
    intro q hq x
    simp only [hfdef, h₀]
    congr 1
    funext k
    rw [hσinv q hq x, map_mul, mul_assoc, hinvφ q hq]
  have hδnn : ∀ a : PositiveRealTorus.intrinsicSubgroup F T₀,
      0 ≤ siegelModulus F (𝓕.M J) T i ν T₀ j a := by
    intro a
    unfold siegelModulus
    exact finprod_nonneg fun β => finprod_nonneg fun _ => pow_nonneg (NNReal.coe_nonneg _) _
  have hfdom : ∀ (a : PositiveRealTorus.intrinsicSubgroup F T₀)
      (x : AdelicGroupPoints F (𝓕.M J)),
      IsSiegelPoint F (𝓕.M J) T i ν T₀ j C t Ω a x → x ∈ normOneSubgroup F (𝓕.M J) →
        f x ≤ ENNReal.ofReal
          (siegelModulus F (𝓕.M J) T i ν T₀ j a / adelicLogHeight F (𝓕.M J) ρM x ^ e) := by
    intro a x hx hxn
    have hpt : ∀ k : K, h₀ (x, k) ≤ ENNReal.ofReal
        (siegelModulus F (𝓕.M J) T i ν T₀ j a / adelicLogHeight F (𝓕.M J) ρM x ^ e) := by
      intro k
      exact ENNReal.ofReal_le_ofReal (sq_div_le_of_siegel_bound (norm_nonneg _) (hσ1 x)
        (rationalLogHeight_mk_le ρM x) (hδnn a) (hB a x hx hxn k k.property))
    calc f x ≤ ∫⁻ _ : K, ENNReal.ofReal
          (siegelModulus F (𝓕.M J) T i ν T₀ j a / adelicLogHeight F (𝓕.M J) ρM x ^ e) ∂μK :=
          lintegral_mono hpt
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  have hlint := hint f hfmeas hfinv hfdom
  -- comparison of the two integrals
  have hB1 : (0 : ℝ) < B ^ 2 + 1 := by positivity
  have heq : ∀ z : K × NormOneRationalQuotient F (𝓕.M J),
      ‖‖g z‖ ^ 2‖ₑ = ENNReal.ofReal (B ^ 2 + 1) *
        h₀ (((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)),
          z.1) := by
    intro z
    set m : AdelicGroupPoints F (𝓕.M J) :=
      ((Quotient.out z.2 : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) with hm
    have hpos : (0 : ℝ) < σ m := lt_of_lt_of_le one_pos (hσ1 m)
    have hnorm : ‖g z‖ = ‖φ (incl m * (z.1 : AdelicGroupPoints F G))‖ * σ m ^ n := by
      simp only [hgdef]
      rw [hσout z.2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    rw [Real.enorm_of_nonneg (by positivity), hnorm, ← ENNReal.ofReal_mul hB1.le,
      mul_div_cancel₀ _ hB1.ne']
  have hint2 : ∫⁻ z, ‖‖g z‖ ^ 2‖ₑ ∂(μK.prod μ₁) =
      ENNReal.ofReal (B ^ 2 + 1) *
        ∫⁻ y : NormOneRationalQuotient F (𝓕.M J),
          f ((Quotient.out y : normOneSubgroup F (𝓕.M J)) : AdelicGroupPoints F (𝓕.M J)) ∂μ₁ := by
    have hae : AEMeasurable (fun z => ‖‖g z‖ ^ 2‖ₑ) (μK.prod μ₁) :=
      (hmeas.norm.pow 2).aemeasurable.enorm
    rw [lintegral_prod_symm (fun z => ‖‖g z‖ ^ 2‖ₑ) hae]
    simp_rw [heq]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext y
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold HasFiniteIntegral
  rw [hint2]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlint

end Langlands.Global
