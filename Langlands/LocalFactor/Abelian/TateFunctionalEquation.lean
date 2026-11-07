import Langlands.LocalFactor.Abelian.TateFourierZeta
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Tate's local functional equation

On the strip where the zeta integrals of `f` for `χ` at `s` and of its plus
Fourier transform for `χ⁻¹` at `1 - s` both converge, the identity
`Z(f̂, χ⁻¹, 1 - s) / L(χ⁻¹, 1 - s) = ε(s) Z(f, χ, s) / L(χ, s)` holds between the
actual integrals. It is proved on the indicators of lattice cosets, which span the
test functions, and transported to every punctured germ of the normal meromorphic
continuations by the identity principle.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology
local notation "addCharOf" ψ =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _ T.topology ψ

theorem lFactorAt_inv_eq (π : F.Carrierˣ) (χ : Character) (a : ℕ) (s : ℂ) :
    (lFactorAt T π χ a s)⁻¹ = if a = 0 then 1 - (χ π : ℂ) * spectralVariable T s else 1 := by
  unfold lFactorAt
  split_ifs <;> simp

theorem exp_log_residueCardinality :
    Complex.exp (Real.log (T.residueCardinality : ℝ) : ℂ) =
      (((T.residueCardinality : ℝ)) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log (residueCardinality_pos' T)]

theorem spectralVariable_one_sub (s : ℂ) :
    spectralVariable T (1 - s) =
      (((T.residueCardinality : ℝ)) : ℂ)⁻¹ * (spectralVariable T s)⁻¹ := by
  rw [spectralVariable, spectralVariable, ← exp_log_residueCardinality, ← Complex.exp_neg,
    ← Complex.exp_neg, ← Complex.exp_add]
  ring_nf

theorem epsilonAt_zero_eq (π : F.Carrierˣ) (χ : Character) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (n : ℤ) (s : ℂ) :
    epsilonAt T π χ ψ μ 0 n s =
      (χ π : ℂ) ^ n * ((((T.residueCardinality : ℝ)) : ℂ) * spectralVariable T s) ^ n *
        ((μ (integerRing T)).toReal : ℂ) := by
  unfold epsilonAt
  rw [ite_eq_left rfl, ← exp_log_residueCardinality, spectralVariable, ← Complex.exp_add,
    ← Complex.exp_int_mul]
  congr 3
  ring

theorem quasicharacter_inv_coe (χ : Character) (v : F.Carrierˣ) :
    ((χ⁻¹ v : ℂˣ) : ℂ) = (χ v : ℂ)⁻¹ := by
  rw [quasicharacter_inv_apply, Units.val_inv_eq_inv_val]

theorem measure_additiveLattice_toReal_coe (μ : LocalHaar) (m : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) =
      (((T.residueCardinality : ℝ)) : ℂ) ^ m * ((μ.measure (integerRing T)).toReal : ℂ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  rw [((HarmonicAnalysis.padicLatticeHaar F T).1 μ m).2.2, integerRing_eq_lattice_zero]
  push_cast
  rfl

theorem one_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have h1 : z = 1 := by linear_combination -h
  rw [h1, norm_one] at hz
  exact lt_irrefl _ hz

/-- The functional equation on the strip for the indicator of one lattice coset, with
its plus Fourier transform written by the lattice Fourier formula. -/
theorem fe_strip_coset (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (χ : Character)
    {a : ℕ} (hχ : ConductorAt T χ a) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) {s : ℂ}
    (hs : ConvergesAt T π χ s) (hs' : ConvergesAt T π χ⁻¹ (1 - s)) (m : ℤ) (b : F.Carrier) :
    letI := T.topology
    letI := borel F.Carrier
    zeta T μ.measure (fun y =>
        ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) * ψ.complex (b * y) *
          (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
            (fun _ => (1 : ℂ)) y) χ⁻¹ (1 - s) *
        (lFactorAt T π χ⁻¹ a (1 - s))⁻¹ =
      epsilonAt T π χ ψ.toAddChar μ.measure a n s *
        zeta T μ.measure ({z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator
          (fun _ => (1 : ℂ))) χ s *
        (lFactorAt T π χ a s)⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hn : n = T.additiveConductor ψ := (additiveConductorAt_iff T ψ n).mp hψ
  have hc0 : (χ π : ℂ) ≠ 0 := (χ π).ne_zero
  have hu0 : spectralVariable T s ≠ 0 := spectralVariable_ne_zero T s
  have hr0 : (((T.residueCardinality : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (residueCardinality_pos' T).ne'
  have hX1 : 1 - (χ π : ℂ) * spectralVariable T s ≠ 0 :=
    one_sub_ne_zero_of_norm_lt_one ((convergesAt_iff_norm_lt_one T π χ s).mp hs)
  have hYeq : (χ⁻¹ π : ℂ) * spectralVariable T (1 - s) =
      (χ π : ℂ)⁻¹ * ((((T.residueCardinality : ℝ)) : ℂ)⁻¹ * (spectralVariable T s)⁻¹) := by
    rw [quasicharacter_inv_coe, spectralVariable_one_sub]
  have hY1 : 1 - (χ π : ℂ)⁻¹ * ((((T.residueCardinality : ℝ)) : ℂ)⁻¹ *
      (spectralVariable T s)⁻¹) ≠ 0 := by
    rw [← hYeq]
    exact one_sub_ne_zero_of_norm_lt_one ((convergesAt_iff_norm_lt_one T π χ⁻¹ (1 - s)).mp hs')
  have hU : ((μ.measure (integralUnits T)).toReal : ℂ) =
      (1 - (((T.residueCardinality : ℝ)) : ℂ)⁻¹) * ((μ.measure (integerRing T)).toReal : ℂ) := by
    rw [(haar_integer_units_masses T μ).2.2]
    push_cast
    rfl
  by_cases hb : b ∈ T.additiveLattice m
  · rw [zeta_fourierCoset_of_mem T μ ψ χ⁻¹ (1 - s) _ m hb, coset_eq_of_mem T m hb, ← hn,
      zeta_additiveLattice T π hπ χ⁻¹ μ hs' (n - m), zeta_additiveLattice T π hπ χ μ hs m,
      setIntegral_integralUnits_characterExtension T μ χ⁻¹ (conductorAt_inv T χ a hχ),
      setIntegral_integralUnits_characterExtension T μ χ hχ, lFactorAt_inv_eq, lFactorAt_inv_eq]
    split_ifs with ha
    · subst ha
      rw [epsilonAt_zero_eq, hYeq, measure_additiveLattice_toReal_coe T μ m, hU]
      exact fe_algebra_lattice hc0 hr0 hu0 n m hX1 hY1
    · simp
  · have hb0 : b ≠ 0 := by
      rintro rfl
      exact hb (T.additiveLattice m).zero_mem
    have hbb : ((Units.mk0 b hb0 : F.Carrierˣ) : F.Carrier) = b := Units.val_mk0 hb0
    rw [← hbb] at hb ⊢
    set bu : F.Carrierˣ := Units.mk0 b hb0
    have hord : T.ord (bu : F.Carrier) < -m := by
      by_contra h
      exact hb ((gauss_valuation_le_exp_iff T bu.ne_zero m).mpr (by omega))
    have hjn : (((-m - T.ord (bu : F.Carrier)).toNat : ℕ) : ℤ) = -m - T.ord (bu : F.Carrier) :=
      Int.toNat_of_nonneg (by omega)
    set j : ℕ := (-m - T.ord (bu : F.Carrier)).toNat with hj
    have hj1 : 1 ≤ j := by omega
    have hidx : T.additiveConductor ψ - m - T.ord (bu : F.Carrier) = n + j := by
      rw [← hn, hjn]
      ring
    rw [zeta_fourierCoset_unit T μ ψ χ s _ (T.additiveConductor ψ - m) bu,
      zeta_coset_of_not_mem T χ hχ μ s m bu hb, hidx, lFactorAt_inv_eq, lFactorAt_inv_eq]
    by_cases ha : a = 0
    · subst ha
      rw [setIntegral_additiveLattice_gauss_unramified T π hπ χ hχ ψ hψ μ hs' j hj1,
        setIntegral_additiveLattice_gauss_base T π hπ χ ψ hψ μ hs',
        setIntegral_integralUnits_characterExtension T μ χ⁻¹ (conductorAt_inv T χ 0 hχ),
        ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (by omega), epsilonAt_zero_eq, hYeq,
        measure_additiveLattice_toReal_coe T μ n, hU]
      have key := fe_algebra_shell (μO := ((μ.measure (integerRing T)).toReal : ℂ))
        hc0 hr0 hu0 n hY1
      linear_combination
        (((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) * ((χ bu : ℂ) *
          Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (bu : F.Carrier)) : ℂ)))) * key
    · rw [setIntegral_additiveLattice_gauss_ramified T π hπ χ hχ ha ψ hψ μ hs' j,
        ite_eq_right ha, ite_eq_right ha]
      by_cases haj : a ≤ j
      · rw [ite_eq_left haj, ite_eq_left (by omega)]
        ring
      · rw [ite_eq_right haj, ite_eq_right (by omega)]
        ring

/-- The plus Fourier transform of a Schwartz–Bruhat function, expanded over the lattice
cosets of its single-lattice expansion. -/
theorem fourierTransform_eq_sum (ψ : AdditiveCharacter) (μ : LocalHaar) (f : TestFunction)
    (m : ℤ) {N : ℕ} (c : Fin N → ℂ) (b : Fin N → F.Carrier)
    (hf : ∀ x, f x = ∑ i : Fin N, c i *
      ({z : F.Carrier | z - b i ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) x)
    (y : F.Carrier) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ f y = ∑ i : Fin N, c i *
      (((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) * ψ.complex (b i * y) *
        (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hL := fun i : Fin N => HarmonicAnalysis.padicLatticeFourier F T ψ μ m (b i) y
  change HarmonicAnalysis.fourierIntegral ψ μ f y = _
  unfold HarmonicAnalysis.fourierIntegral
  have hsum : (fun x => ψ.complex (x * y) * f x) = fun x => ∑ i : Fin N, c i *
      (ψ.complex (x * y) *
        ({z : F.Carrier | z - b i ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) x) := by
    funext x
    rw [hf x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, integral_finsetSum _ (fun i _ => (hL i).1.const_mul (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  congr 1
  exact (hL i).2

/-- The zeta integrand of a function times a set indicator. -/
theorem zetaIntegrand_mul_indicator (g : F.Carrier → ℂ) (L : Set F.Carrier) (χ : Character)
    (s : ℂ) :
    zetaIntegrand T (fun y => g y * L.indicator (fun _ => (1 : ℂ)) y) χ s =
      fun y => g y * zetaIntegrand T (L.indicator (fun _ => (1 : ℂ))) χ s y := by
  funext y
  unfold zetaIntegrand
  split_ifs <;> ring

/-- Tate's functional equation between the actual convergent integrals on the strip. -/
theorem fe_strip (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (χ : Character)
    {a : ℕ} (hχ : ConductorAt T χ a) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) (f : TestFunction) {s : ℂ}
    (hs : ConvergesAt T π χ s) (hs' : ConvergesAt T π χ⁻¹ (1 - s)) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    zeta T μ.measure (HarmonicAnalysis.fourierTransform ψ μ f) χ⁻¹ (1 - s) *
        (lFactorAt T π χ⁻¹ a (1 - s))⁻¹ =
      epsilonAt T π χ ψ.toAddChar μ.measure a n s * zeta T μ.measure f χ s *
        (lFactorAt T π χ a s)⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  obtain ⟨m, N, c, b, hf⟩ := HarmonicAnalysis.padicLatticeSchwartzExpansion F T f
  set Lm : ℂ := ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ) with hLm
  set Ld : Set F.Carrier := (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier)
    with hLd
  set φ : Fin N → F.Carrier → ℂ := fun i y =>
    Lm * ψ.complex (b i * y) * Ld.indicator (fun _ => (1 : ℂ)) y with hφ
  set C : Fin N → F.Carrier → ℂ := fun i =>
    {z : F.Carrier | z - b i ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ)) with hC
  have hzf : zeta T μ.measure f χ s = ∑ i : Fin N, c i * zeta T μ.measure (C i) χ s :=
    zeta_finset_sum T Finset.univ c C f hf μ.measure χ s
      (fun i _ => zeta_integrable T π hπ χ μ (cosetTest T m (b i)) s hs)
  have hint : ∀ i, Integrable (zetaIntegrand T (φ i) χ⁻¹ (1 - s)) μ.measure := by
    intro i
    have h1 := zeta_integrable T π hπ χ⁻¹ μ (cosetTest T (T.additiveConductor ψ - m) 0)
      (1 - s) hs'
    rw [cosetTest_coe, coset_zero] at h1
    have hpt : zetaIntegrand T (φ i) χ⁻¹ (1 - s) = fun y => (Lm * ψ.complex (b i * y)) *
        zetaIntegrand T (Ld.indicator (fun _ => (1 : ℂ))) χ⁻¹ (1 - s) y :=
      zetaIntegrand_mul_indicator T (fun y => Lm * ψ.complex (b i * y)) Ld χ⁻¹ (1 - s)
    rw [hpt]
    refine h1.bdd_mul (c := ‖Lm‖) ?_ (Eventually.of_forall fun y => ?_)
    · exact (continuous_const.mul (ψ.continuous_complex.comp
        (continuous_const.mul continuous_id))).aestronglyMeasurable
    · rw [norm_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex, mul_one]
  have hzF : zeta T μ.measure (HarmonicAnalysis.fourierTransform ψ μ f) χ⁻¹ (1 - s) =
      ∑ i : Fin N, c i * zeta T μ.measure (φ i) χ⁻¹ (1 - s) :=
    zeta_finset_sum T Finset.univ c φ _ (fourierTransform_eq_sum T ψ μ f m c b hf) μ.measure
      χ⁻¹ (1 - s) (fun i _ => hint i)
  rw [hzf, hzF, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := fe_strip_coset T π hπ χ hχ ψ hψ μ hs hs' m (b i)
  calc c i * zeta T μ.measure (φ i) χ⁻¹ (1 - s) * (lFactorAt T π χ⁻¹ a (1 - s))⁻¹ =
      c i * (zeta T μ.measure (φ i) χ⁻¹ (1 - s) * (lFactorAt T π χ⁻¹ a (1 - s))⁻¹) := by ring
    _ = c i * (epsilonAt T π χ ψ.toAddChar μ.measure a n s * zeta T μ.measure (C i) χ s *
        (lFactorAt T π χ a s)⁻¹) := by rw [h]
    _ = _ := by ring

/-- Some point lies in the strip where both zeta integrals converge. -/
theorem exists_convergesAt_strip (π : F.Carrierˣ) (χ : Character) :
    ∃ s : ℂ, ConvergesAt T π χ s ∧ ConvergesAt T π χ⁻¹ (1 - s) := by
  have hq : 0 < Real.log (T.residueCardinality : ℝ) :=
    Real.log_pos (by exact_mod_cast T.residueCardinality_gt_one)
  have hχ0 : 0 < ‖(χ π : ℂ)‖ := norm_pos_iff.mpr (χ π).ne_zero
  set r : ℝ := 1 / 2 + Real.log ‖(χ π : ℂ)‖ / Real.log (T.residueCardinality : ℝ) with hr
  have hhalf : Real.exp (-(1 / 2) * Real.log (T.residueCardinality : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  refine ⟨(r : ℂ), ?_, ?_⟩
  · unfold ConvergesAt
    rw [Complex.ofReal_re]
    have he : ‖(χ π : ℂ)‖ * Real.exp (-r * Real.log (T.residueCardinality : ℝ)) =
        Real.exp (-(1 / 2) * Real.log (T.residueCardinality : ℝ)) := by
      rw [← Real.exp_log hχ0, ← Real.exp_add]
      congr 1
      rw [hr]
      field_simp
      ring
    rw [he]
    exact hhalf
  · unfold ConvergesAt
    rw [quasicharacter_inv_coe, norm_inv, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    have he : ‖(χ π : ℂ)‖⁻¹ * Real.exp (-(1 - r) * Real.log (T.residueCardinality : ℝ)) =
        Real.exp (-(1 / 2) * Real.log (T.residueCardinality : ℝ)) := by
      rw [← Real.exp_log hχ0, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      rw [hr]
      field_simp
      ring
    rw [he]
    exact hhalf

/-- Tate's local functional equation for every test function: the plus Fourier transform
is a test function, and for any normal meromorphic continuations of the two zeta
integrals the normalized quotients agree on every punctured neighbourhood. -/
theorem fourier_functional_equation (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) (f : TestFunction) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∃ g : TestFunction,
      (∀ y, g y = HarmonicAnalysis.fourierTransform ψ μ f y) ∧
      ∀ Z Y : ℂ → ℂ, ExtendsIntegral T π μ.measure f χ Z →
        ExtendsIntegral T π μ.measure g χ⁻¹ Y →
        ∀ s₀ : ℂ,
          (fun s => Y (1 - s) / lFactorAt T π χ⁻¹ a (1 - s))
            =ᶠ[𝓝[≠] s₀]
          (fun s => epsilonAt T π χ ψ.toAddChar μ.measure a n s *
            (Z s / lFactorAt T π χ a s)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hcl := HarmonicAnalysis.padicFourierClosure p F T ψ.toAddChar ψ.continuous_toFun
    ψ.nontrivial μ.measure inferInstance f f.locallyConstant f.hasCompactSupport
  let g : TestFunction :=
    ⟨Fourier.fourierIntegral ψ.toAddChar⁻¹ μ.measure f, hcl.2.2.2.1, hcl.2.2.2.2.1⟩
  have hg : ∀ y, g y = HarmonicAnalysis.fourierTransform ψ μ f y := fun y => hcl.2.2.1 y
  refine ⟨g, hg, ?_⟩
  intro Z Y hZ hY s₀
  have hgf : (g : F.Carrier → ℂ) = HarmonicAnalysis.fourierTransform ψ μ f := funext hg
  have hm1 : MeromorphicOn (fun s => Y (1 - s) / lFactorAt T π χ⁻¹ a (1 - s)) Set.univ := by
    intro s _
    have han : AnalyticAt ℂ (fun z : ℂ => 1 - z) s := analyticAt_const.sub analyticAt_id
    exact ((hY.1 (Set.mem_univ (1 - s))).meromorphicAt.comp_analyticAt han).div
      (((lFactorAt_meromorphicNFOn T π χ⁻¹ a) (Set.mem_univ (1 - s))).meromorphicAt.comp_analyticAt
        han)
  have hm2 : MeromorphicOn (fun s => epsilonAt T π χ ψ.toAddChar μ.measure a n s *
      (Z s / lFactorAt T π χ a s)) Set.univ := by
    intro s _
    exact (Differentiable.analyticAt (epsilonAt_differentiable T π χ ψ.toAddChar μ.measure a n)
      s).meromorphicAt.mul ((hZ.1 (Set.mem_univ s)).meromorphicAt.div
        ((lFactorAt_meromorphicNFOn T π χ a) (Set.mem_univ s)).meromorphicAt)
  obtain ⟨s₁, hs₁, hs₁'⟩ := exists_convergesAt_strip T π χ
  have hW : IsOpen {s : ℂ | ConvergesAt T π χ s ∧ ConvergesAt T π χ⁻¹ (1 - s)} :=
    (isOpen_convergesAt T π χ).inter
      ((isOpen_convergesAt T π χ⁻¹).preimage (continuous_const.sub continuous_id))
  have he : (fun s => Y (1 - s) / lFactorAt T π χ⁻¹ a (1 - s)) =ᶠ[𝓝 s₁]
      (fun s => epsilonAt T π χ ψ.toAddChar μ.measure a n s * (Z s / lFactorAt T π χ a s)) := by
    filter_upwards [hW.mem_nhds ⟨hs₁, hs₁'⟩] with s hs
    rw [hY.2 (1 - s) hs.2, hZ.2 s hs.1, hgf, div_eq_mul_inv, div_eq_mul_inv,
      fe_strip T π hπ χ hχ ψ hψ μ f hs.1 hs.2]
    ring
  exact meromorphic_germ_eq_of_eventuallyEq hm1 hm2 he s₀

end Langlands.LocalFactor.PadicAbelian
