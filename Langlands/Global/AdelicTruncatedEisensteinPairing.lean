import Langlands.Global.ArthurSiegelSets
import Langlands.Global.ArthurCuspidalRepresentativeBounds
import Langlands.Global.AdelicTemperedVanishingReduction
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.RealDeriv

/-! # The truncated and the regularized Eisenstein pairings of Delorme 2023, §7

P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023), §7, pp.22–25: the two
sides of the asymptotic identity of Theorem 7.1, for a compatible family of standard parabolics
of a connected reductive group over a number field and a compact subgroup `K` with
`P_0(𝔸) K = G(𝔸)`.

* `ArthurTruncation.characteristicChamber`, `characteristicProduct`, `characteristicRegion`: the
  convex set `C_T^G ⊂ 𝔞_0^G`, the product `Ω_{N_0} M_0(C_T^G) K ⊂ G(𝔸)^1` and its image
  `𝒞_T^G` in `G(F) \ G(𝔸)^1` (p.23);
* `StandardParabolicFamily.truncatedPairing`: `Ω^T_{P_0}(E, Φ)^Z = ∫_{𝒞_T^G} E^Z conj Φ^Z`
  (Theorem 7.1);
* `negativeOrthantRegularizedIntegral`: the regularized integral of `e^{⟨z, c⟩} P(c)` over the
  negative orthant, in closed form, with its comparison to the convergent integral and to
  differentiation in `z` (the positive Fourier convention of (7.10)–(7.11));
* `StandardParabolicFamily.UnitaryPairingExpansion`, `IsSquareIntegrableTwistDecomposition`,
  `IsNormalizedPairingExpansion`, `IsWeakConstantTermPairingExpansion`, `regularizedPairing`: the
  finite unitary exponent and polynomial data on `𝔞_Q^G`, in coroot coordinates, of Delorme's
  extended pairings `p_Q` (the pairing (3.7) of the twisted square-integrable part of the first
  argument, p.15), their relation to the actual weak constant terms, and the finite sum
  `ω^T_{P_0}` of the regularized integrals (7.8)–(7.12);
* `StandardParabolicFamily.AffineExponentLabels`, `genericParameterRegion`: fixed affine exponent
  labels `λ ↦ sλ − μ` of (7.12) and the parameter region where no `θ_Q` of a label vanishes. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set Filter Topology
open scoped CategoryTheory.MonObj Classical Pointwise

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

variable (ν) in
/-- **Delorme's convex set `C_T^G`** (Delorme 2023, §7, p.23, for `Q = G`): the `X ∈ 𝔞_0^G` with
`α(X − T_0) ≥ 0` and `ϖ_α(X − T) ≤ 0` for every simple root `α ∈ Δ_0`. Here `𝔞_0 = V T`,
`𝔞_0^G` is the real span of the coroots `D.realCorootSpan`, `α(H) = eval T α H`, and
`ϖ_α = ArthurRelative.weight … Δ_0 α` is the fundamental weight of `Δ̂_0` (the weights of the
truncated Siegel sets of `ArthurSiegelSets` for `P = G`). -/
def characteristicChamber (T₀ Tp : V T) : Set (V T) :=
  {X | X ∈ D.realCorootSpan ∧ ∀ β ∈ simpleFinset ν hG hi,
    0 ≤ eval T β (X - T₀) ∧
      ArthurRelative.weight hG hi ν D (simpleFinset ν hG hi : Set (characterLattice T)) β
        (X - Tp) ≤ 0}

/-- **`M_0(C)`** (Delorme 2023, §7, p.22): the points `m ∈ M_0(𝔸) ∩ G(𝔸)^1` with `H_0(m) ∈ C`,
as points of `G(𝔸)`. `M_0` is the standard minimal Levi `Standard.leviScheme i ν ∅`, `G(𝔸)^1` is
`normOneSubgroup F G` and `H_0 = height hi hK hρ` is the Iwasawa height of `K` for `P_0`, read in
`𝔞_0 = V T`. -/
def leviHeightSet (C : Set (V T)) : Set (AdelicGroupPoints F G) :=
  {x | ∃ m : AdelicGroupPoints F (Standard.leviScheme i ν ∅),
    map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m = x ∧
      x ∈ normOneSubgroup F G ∧ height hi hK hρ x ∈ C}

/-- **The product `Ω_{N_0} M_0(C_T^G) K`** (Delorme 2023, §7, p.23): the products `n m k` of a
point `n` of the compact set `Ω_{N_0} = C.omegaN ⊆ N_0(𝔸)` of the Siegel domain data `C`, a point
`m ∈ M_0(C_T^G)` and `k ∈ K`, in `G(𝔸)`. -/
def characteristicProduct
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₀ Tp : V T) : Set (AdelicGroupPoints F G) :=
  (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) '' C.omegaN) *
    leviHeightSet hi hK hρ (characteristicChamber ν hG hi D T₀ Tp) *
      (K : Set (AdelicGroupPoints F G))

/-- **The region `𝒞_T^G = G(F) Ω_{N_0} M_0(C_T^G) K`** (Delorme 2023, §7, p.23): the image in
`G(F) \ G(𝔸)^1` (`NormOneRationalQuotient F G`) of the norm-one points of
`characteristicProduct`. -/
def characteristicRegion
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (T₀ Tp : V T) : Set (NormOneRationalQuotient F G) :=
  LeftCosetSpace.mk (rationalNormOneSubgroup F G) ''
    {x : normOneSubgroup F G |
      (x : AdelicGroupPoints F G) ∈ characteristicProduct hG hi D hK hρ C T₀ Tp}

/-- **Delorme's (7.1)** for the Siegel domain data `C`: `N_0(𝔸) = N_0(F) Ω_{N_0}` and
`M_0(𝔸)^1 = M_0(F) Ω_{M_0^1}`. -/
def IsRationalCovering
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)) :
    Prop :=
  (∀ n : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅),
    ∃ r ∈ rationalSubgroup F (Standard.unipotentScheme i ν ∅), ∃ ω ∈ C.omegaN, n = r * ω) ∧
  ∀ m : normOneSubgroup F (Standard.leviScheme i ν ∅),
    ∃ r : RationalGroupPoints F (Standard.leviScheme i ν ∅), ∃ ω ∈ C.omegaM,
      (m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)) =
        rational F (Standard.leviScheme i ν ∅) r * (ω : AdelicGroupPoints F _)

end Langlands.Global.ArthurTruncation

namespace Langlands.Global

/-! ### The regularized integral over the negative orthant -/

section Orthant

theorem norm_pow_mul_cexp (a : ℂ) (k : ℕ) (x : ℝ) :
    ‖(x : ℂ) ^ k * Complex.exp (a * x)‖ = |x| ^ k * Real.exp (a.re * x) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, Complex.re_mul_ofReal,
    Real.norm_eq_abs]

/-- `x ↦ x^k e^{a x}` is integrable on `(−∞, 0]` when `Re a > 0`. -/
theorem integrableOn_Iic_pow_mul_cexp {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ k * Complex.exp (a * x)) (Iic 0) := by
  have hk : (-1 : ℝ) < k := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have hreal : IntegrableOn (fun u : ℝ => u ^ (k : ℝ) * Real.exp (-a.re * u ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hk one_pos ha
  have hreal' : IntegrableOn (fun u : ℝ => |u| ^ k * Real.exp (-a.re * u)) (Ici (-0)) := by
    rw [neg_zero, integrableOn_Ici_iff_integrableOn_Ioi]
    refine hreal.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu' : (0 : ℝ) < u := hu
    dsimp only
    rw [abs_of_pos hu', Real.rpow_natCast, Real.rpow_one]
  have hneg : IntegrableOn (fun x : ℝ => |-x| ^ k * Real.exp (-a.re * -x)) (Iic 0) :=
    hreal'.comp_neg_Iic
  refine Integrable.mono' hneg ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ =>
      (x : ℂ) ^ k * Complex.exp (a * x)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_pow_mul_cexp, abs_neg, neg_mul_neg]

theorem tendsto_pow_mul_cexp_atBot {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ k * Complex.exp (a * x)) atBot (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) a.re ha).comp
    tendsto_neg_atBot_atTop
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_lt_atBot 0] with x hx
  rw [norm_pow_mul_cexp, Function.comp_apply, abs_of_neg hx, Real.rpow_natCast, neg_mul_neg]

/-- `∫_{−∞}^0 x^k e^{a x} dx = (−1)^k k! / a^{k+1}` for `Re a > 0`. -/
theorem integral_Iic_pow_mul_cexp {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    ∫ x in Iic (0 : ℝ), (x : ℂ) ^ k * Complex.exp (a * x) =
      (-1) ^ k * (k.factorial : ℂ) / a ^ (k + 1) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  induction k with
  | zero =>
    have := integral_exp_mul_complex_Iic ha 0
    simpa using this
  | succ k ih =>
    have hderiv : ∀ x ∈ Iic (0 : ℝ), HasDerivAt
        (fun x : ℝ => (x : ℂ) ^ (k + 1) * Complex.exp (a * x))
        (((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ k * Complex.exp (a * x) +
          a * ((x : ℂ) ^ (k + 1) * Complex.exp (a * x))) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℂ => y ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ k)
          (x : ℂ) := by
        simpa using hasDerivAt_pow (k + 1) (x : ℂ)
      have h2 : HasDerivAt (fun y : ℂ => Complex.exp (a * y)) (Complex.exp (a * x) * a) (x : ℂ) :=
        ((hasDerivAt_id (x : ℂ)).const_mul a).cexp.congr_deriv (by simp)
      have h3 := (h1.mul h2).comp_ofReal
      convert h3 using 1
      ring
    have hint1 := (integrableOn_Iic_pow_mul_cexp ha k).const_mul (((k + 1 : ℕ) : ℂ))
    have hint2 := (integrableOn_Iic_pow_mul_cexp ha (k + 1)).const_mul a
    have hint1' : IntegrableOn (fun x : ℝ => ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ k *
        Complex.exp (a * x)) (Iic 0) :=
      IntegrableOn.congr_fun hint1 (fun x _ => by ring) measurableSet_Iic
    have hsum : IntegrableOn (fun x : ℝ => ((k + 1 : ℕ) : ℂ) * (x : ℂ) ^ k * Complex.exp (a * x) +
        a * ((x : ℂ) ^ (k + 1) * Complex.exp (a * x))) (Iic 0) :=
      Integrable.add hint1' hint2
    have hftc := integral_Iic_of_hasDerivAt_of_tendsto' hderiv hsum
      (tendsto_pow_mul_cexp_atBot ha (k + 1))
    rw [integral_add hint1' hint2] at hftc
    simp only [mul_assoc] at hftc
    rw [integral_const_mul, integral_const_mul, ih] at hftc
    simp only [Complex.ofReal_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, mul_zero, sub_zero] at hftc
    have hI : ∫ x in Iic (0 : ℝ), (x : ℂ) ^ (k + 1) * Complex.exp (a * x) =
        -(((k + 1 : ℕ) : ℂ) * ((-1) ^ k * (k.factorial : ℂ) / a ^ (k + 1))) / a := by
      rw [eq_div_iff ha0]
      linear_combination hftc
    rw [hI, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The one-variable factor `(−1)^n n! / s^{n+1}`, the value at `s` of the regularized integral
`∫*_{−∞}^0 c^n e^{s c} dc` (`integral_Iic_pow_mul_cexp`). -/
def orthantFactor (n : ℕ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * (n.factorial : ℂ) / s ^ (n + 1)

theorem hasDerivAt_orthantFactor {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    HasDerivAt (orthantFactor n) (orthantFactor (n + 1) s) s := by
  have h := ((hasDerivAt_pow (n + 1) s).inv (pow_ne_zero _ hs)).const_mul
    ((-1 : ℂ) ^ n * (n.factorial : ℂ))
  convert h using 1
  · funext t
    simp [orthantFactor, div_eq_mul_inv]
  · simp only [orthantFactor, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **The regularized integral over the negative orthant**
`∫*_{c ∈ (−∞, 0]^σ} e^{∑_α z_α c_α} P(c) dc = ∑_k P_k ∏_α (−1)^{k_α} k_α! / z_α^{k_α + 1}` of a
polynomial `P = ∑_k P_k c^k`. It is a rational function of `z`, regular where every `z_α ≠ 0`. For
`Re z_α > 0` it is the convergent integral (`negativeOrthantRegularizedIntegral_eq_integral`), so
it is the meromorphic continuation used by Delorme 2023, §7, p.24, to define `∫*`. -/
def negativeOrthantRegularizedIntegral {σ : Type*} [Fintype σ] (z : σ → ℂ)
    (P : MvPolynomial σ ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * ∏ α, orthantFactor (k α) (z α)

/-- For `Re z_α > 0` the closed form is the integral over the negative orthant. -/
theorem negativeOrthantRegularizedIntegral_eq_integral {σ : Type*} [Fintype σ] {z : σ → ℂ}
    (hz : ∀ α, 0 < (z α).re) (P : MvPolynomial σ ℂ) :
    negativeOrthantRegularizedIntegral z P =
      ∫ c in Set.univ.pi (fun _ : σ => Iic (0 : ℝ)),
        Complex.exp (∑ α, z α * c α) * MvPolynomial.eval (fun α => (c α : ℂ)) P := by
  have hμ : (volume : Measure (σ → ℝ)).restrict (Set.univ.pi fun _ => Iic (0 : ℝ)) =
      Measure.pi (fun _ => (volume : Measure ℝ).restrict (Iic 0)) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hterm : ∀ c : σ → ℝ, Complex.exp (∑ α, z α * c α) *
      MvPolynomial.eval (fun α => (c α : ℂ)) P =
        ∑ d ∈ P.support, P.coeff d * ∏ α, ((c α : ℂ) ^ d α * Complex.exp (z α * c α)) := by
    intro c
    rw [MvPolynomial.eval_eq', Finset.mul_sum, Complex.exp_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [hμ]
  simp_rw [hterm]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, integral_fintype_prod_eq_prod
      (fun α (t : ℝ) => (t : ℂ) ^ d α * Complex.exp (z α * t))]
    congr 1
    refine Finset.prod_congr rfl fun α _ => ?_
    exact (integral_Iic_pow_mul_cexp (hz α) (d α)).symm
  · intro d _
    exact (Integrable.fintype_prod fun α =>
      integrableOn_Iic_pow_mul_cexp (hz α) (d α)).const_mul _

/-- (7.8) in coroot coordinates: the regularized integral of `e^{⟨z, c⟩}` is `(∏_α z_α)^{-1}`. -/
theorem negativeOrthantRegularizedIntegral_one {σ : Type*} [Fintype σ] (z : σ → ℂ) :
    negativeOrthantRegularizedIntegral z 1 = (∏ α, z α)⁻¹ := by
  simp [negativeOrthantRegularizedIntegral, orthantFactor, MvPolynomial.support_one]

/-- **The positive Fourier transform** (Delorme 2023, (7.10)) in coordinates:
`ℱ_+ f(w) = ∫ f(x) e^{∑_α w_α x_α} dx`. For `w = λ(α̌)` with `λ ∈ i𝔞_Q^{G,*}` this is Delorme's
`ℱφ(λ) = ∫ φ(X) e^{⟨λ, X⟩} dX` in the coroot coordinates `X = ∑_α x_α α̌`, up to the factor
`C_Q` relating `dX` to `dx`. -/
def positiveFourierTransform {σ : Type*} [Fintype σ] (f : (σ → ℝ) → ℂ) (w : σ → ℂ) : ℂ :=
  ∫ x, f x * Complex.exp (∑ α, w α * x α)

/-- For `Re z_α > 0` the regularized integral is the positive Fourier transform of `P` times the
indicator of the negative orthant. -/
theorem negativeOrthantRegularizedIntegral_eq_positiveFourierTransform {σ : Type*} [Fintype σ]
    {z : σ → ℂ} (hz : ∀ α, 0 < (z α).re) (P : MvPolynomial σ ℂ) :
    negativeOrthantRegularizedIntegral z P =
      positiveFourierTransform ((Set.univ.pi fun _ : σ => Iic (0 : ℝ)).indicator
        fun c => MvPolynomial.eval (fun α => (c α : ℂ)) P) z := by
  rw [negativeOrthantRegularizedIntegral_eq_integral hz, positiveFourierTransform]
  have hs : MeasurableSet (Set.univ.pi fun _ : σ => Iic (0 : ℝ)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Iic
  have hfun : (fun c : σ → ℝ => (Set.univ.pi fun _ : σ => Iic (0 : ℝ)).indicator
      (fun c => MvPolynomial.eval (fun α => (c α : ℂ)) P) c *
        Complex.exp (∑ α, z α * (c α : ℂ))) =
      (Set.univ.pi fun _ : σ => Iic (0 : ℝ)).indicator (fun c => Complex.exp (∑ α, z α * c α) *
        MvPolynomial.eval (fun α => (c α : ℂ)) P) := by
    funext c
    by_cases hc : c ∈ Set.univ.pi fun _ : σ => Iic (0 : ℝ)
    · simp only [Set.indicator_of_mem hc]
      ring
    · simp only [Set.indicator_of_notMem hc, zero_mul]
  rw [hfun, integral_indicator hs]

/-- The complex partial derivative `∂_α h(w) = d/ds h(w with w_α = s)` at `s = w_α`. With
`w_α = i ξ_α` on the imaginary axis it is `D_α = (1/i) ∂/∂ξ_α` for holomorphic `h`. -/
def coordinatePartial {σ : Type*} (α : σ) (h : (σ → ℂ) → ℂ) : (σ → ℂ) → ℂ :=
  fun w => deriv (fun s : ℂ => h (Function.update w α s)) (w α)

/-- The monomial operator `∂^k = ∏_α ∂_α^{k_α}`, applying the partial derivatives in the order of
`(Finsupp.toMultiset k).toList` (they commute on holomorphic functions). -/
def monomialPartial {σ : Type*} (k : σ →₀ ℕ) (h : (σ → ℂ) → ℂ) : (σ → ℂ) → ℂ :=
  (Finsupp.toMultiset k).toList.foldr coordinatePartial h

/-- **The operator `P(∂)` of a polynomial symbol** `P = ∑_k P_k x^k`:
`P(∂) h = ∑_k P_k ∂^k h`, with the positive convention `ℱ_+(P f) = P(∂) ℱ_+ f` of Delorme 2023,
(7.11): the coordinate `x_α` acts as `∂_α` (`coordinatePartial_negativeOrthantRegularizedIntegral`).
-/
def polynomialSymbolOperator {σ : Type*} (P : MvPolynomial σ ℂ) (h : (σ → ℂ) → ℂ) :
    (σ → ℂ) → ℂ :=
  fun w => ∑ k ∈ P.support, P.coeff k * monomialPartial k h w

/-- **The positive convention (7.11) on the negative orthant.** Multiplying the symbol by the
coordinate `x_α` differentiates the regularized integral in `z_α`, wherever `z_α ≠ 0`. -/
theorem hasDerivAt_negativeOrthantRegularizedIntegral {σ : Type*} [Fintype σ] {z : σ → ℂ}
    (α : σ) (hα : z α ≠ 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun s : ℂ => negativeOrthantRegularizedIntegral (Function.update z α s) P)
      (negativeOrthantRegularizedIntegral z (MvPolynomial.X α * P)) (z α) := by
  have hfac : ∀ k : σ →₀ ℕ, HasDerivAt
      (fun s : ℂ => ∏ β, orthantFactor (k β) (Function.update z α s β))
      (∏ β, orthantFactor ((Finsupp.single α 1 + k : σ →₀ ℕ) β) (z β)) (z α) := by
    intro k
    have hupd : ∀ s : ℂ, (fun β => orthantFactor (k β) (Function.update z α s β)) =
        Function.update (fun β => orthantFactor (k β) (z β)) α (orthantFactor (k α) s) := by
      intro s
      funext β
      by_cases h : β = α
      · subst h
        simp
      · simp [Function.update_of_ne h]
    have hupd' : (fun β => orthantFactor ((Finsupp.single α 1 + k : σ →₀ ℕ) β) (z β)) =
        Function.update (fun β => orthantFactor (k β) (z β)) α
          (orthantFactor (k α + 1) (z α)) := by
      funext β
      by_cases h : β = α
      · subst h
        simp [add_comm]
      · simp [Function.update_of_ne h, Ne.symm h]
    simp_rw [hupd, hupd', Finset.prod_update_of_mem (Finset.mem_univ α)]
    exact (hasDerivAt_orthantFactor hα (k α)).mul_const _
  unfold negativeOrthantRegularizedIntegral
  rw [MvPolynomial.support_X_mul, Finset.sum_map]
  simp only [addLeftEmbedding_apply, MvPolynomial.coeff_X_mul]
  exact HasDerivAt.fun_sum fun k _ => (hfac k).const_mul _

theorem coordinatePartial_negativeOrthantRegularizedIntegral {σ : Type*} [Fintype σ] {z : σ → ℂ}
    (α : σ) (hα : z α ≠ 0) (P : MvPolynomial σ ℂ) :
    coordinatePartial α (fun w => negativeOrthantRegularizedIntegral w P) z =
      negativeOrthantRegularizedIntegral z (MvPolynomial.X α * P) :=
  (hasDerivAt_negativeOrthantRegularizedIntegral α hα P).deriv

/-- The translate `c ↦ P(t + c)` of a polynomial. -/
def polynomialShift {σ : Type*} (t : σ → ℝ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.aeval (fun α => MvPolynomial.X α + MvPolynomial.C ((t α : ℝ) : ℂ)) P

end Orthant

namespace StandardParabolicFamily

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces AdelicSiegelFactors Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G) {K : Subgroup (AdelicGroupPoints F G)}

/-! ### The truncated pairing `Ω^T_{P_0}` -/

/-- `P_∅(𝔸) K = G(𝔸)` for the canonical representative `Standard.parabolicHom i ν ∅` of the
minimal standard parabolic of the family. -/
theorem isIwasawaCompact_standardBot (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K) :
    IsIwasawaCompact (Standard.parabolicHom 𝓕.i 𝓕.ν ∅) K :=
  hK.of_range_eq ((𝓕.isCompatible 𝓕.bot).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom 𝓕.i 𝓕.ν ∅).2.symm)

/-- Restriction `X^*(P_0) ⊗ ℝ → X^*(T) ⊗ ℝ` is bijective (the published
`ArthurTruncation.bijective_restrictToTorus_minimal`). -/
theorem bijective_restrictToTorus_bot : Function.Bijective (restrictToTorus F 𝓕.i 𝓕.ν ∅) :=
  ArthurTruncation.bijective_restrictToTorus_minimal F G 𝓕.T 𝓕.i 𝓕.ν 𝓕.connectedReductive
    𝓕.maximalSplit 𝓕.generic

/-- The height `H_0 : G(𝔸) → 𝔞_0 = V T` of `K` for the minimal standard parabolic. -/
def minimalHeight (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K) (x : AdelicGroupPoints F G) : V 𝓕.T :=
  ArthurTruncation.height 𝓕.maximalSplit (𝓕.isIwasawaCompact_standardBot hK)
    𝓕.bijective_restrictToTorus_bot x

/-- **`𝒞_T^G`** for the family: `ArthurTruncation.characteristicRegion` for its torus, generic
cocharacter, coroots and `K`. -/
def truncationRegion (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅)
      (Standard.leviScheme 𝓕.i 𝓕.ν ∅))
    (T₀ Tp : V 𝓕.T) : Set (NormOneRationalQuotient F G) :=
  ArthurTruncation.characteristicRegion 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.coroots
    (𝓕.isIwasawaCompact_standardBot hK) 𝓕.bijective_restrictToTorus_bot C T₀ Tp

/-- The point `exp Z` of `G(𝔸)` attached to `z ∈ 𝔄_G = A_G^∞` (`positiveSplitComponent` of the
top index), with `Z = H_G(z)`. -/
def centralPoint (z : 𝓕.positiveSplitComponent 𝓕.top) : AdelicGroupPoints F G :=
  map F (𝓕.P 𝓕.top) G (𝓕.p 𝓕.top) z

/-- The central translate `Φ^Z(g) = Φ(g exp Z)`. -/
def centralTranslate (z : 𝓕.positiveSplitComponent 𝓕.top) (f : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  fun g => f (g * 𝓕.centralPoint z)

/-- The integrand `y ↦ E(ẏ exp Z) conj Φ(ẏ exp Z)` of `Ω^T` on `G(F) \ G(𝔸)^1`, evaluated at the
chosen representative `ẏ = Quotient.out y ∈ G(𝔸)^1` of `y`. -/
def truncatedPairingIntegrand (z : 𝓕.positiveSplitComponent 𝓕.top)
    (E Φ : AdelicGroupPoints F G → ℂ) : NormOneRationalQuotient F G → ℂ :=
  fun y => 𝓕.centralTranslate z E ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G) *
    starRingEnd ℂ (𝓕.centralTranslate z Φ
      ((Quotient.out y : normOneSubgroup F G) : AdelicGroupPoints F G))

/-- **`Ω^T_{P_0}(E, Φ)^Z = ∫_{𝒞_T^G} E(x, λ)^Z conj Φ^Z(x) dx`** (Delorme 2023, Theorem 7.1), for
the norm-one quotient Haar measure `normOneRationalQuotientHaarMeasure F G`. -/
def truncatedPairing (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme 𝓕.i 𝓕.ν ∅)
      (Standard.leviScheme 𝓕.i 𝓕.ν ∅))
    (T₀ Tp : V 𝓕.T) (z : 𝓕.positiveSplitComponent 𝓕.top) (E Φ : AdelicGroupPoints F G → ℂ) :
    ℂ :=
  ∫ y in 𝓕.truncationRegion hK C T₀ Tp, 𝓕.truncatedPairingIntegrand z E Φ y
    ∂normOneRationalQuotientHaarMeasure F G

/-! ### Coroot coordinates on `𝔞_Q^G` -/

/-- `Δ_Q`, indexed by `Δ_0 ∖ Δ_0^Q`: the simple roots of `Δ_0` outside `Q.1 = Δ_0^Q`. -/
def relativeSimpleRoots (Q : StandardIndex F G 𝓕.i 𝓕.ν) : Finset (characterLattice 𝓕.T) :=
  (ArthurTruncation.simpleFinset 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit).filter (· ∉ Q.1)

omit [NumberField F] in
theorem mem_relativeRoots_of_mem_relativeSimpleRoots (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (α : 𝓕.relativeSimpleRoots Q) : (α : characterLattice 𝓕.T) ∈ relativeRoots 𝓕.i := by
  have h := (Finset.mem_filter.mp α.2).1
  rw [ArthurTruncation.mem_simpleFinset] at h
  exact simpleRelativeRoots_subset_relativeRoots 𝓕.i 𝓕.ν h

/-- The projection `𝔞_0 = V T → 𝔞_Q = Hom(X^*(P_Q), ℝ)`, `H ↦ (χ ↦ ⟨χ|_T, H⟩)`: the transpose of
restriction of characters `chamberEmbedding Q`. -/
def splitDual (Q : StandardIndex F G 𝓕.i 𝓕.ν) : V 𝓕.T →ₗ[ℝ] RealCharacterDual F (𝓕.P Q) where
  toFun v :=
    { toFun := fun χ => pair 𝓕.T (𝓕.chamberEmbedding Q ((1 : ℝ) ⊗ₜ[ℤ] χ)) v
      map_zero' := by simp
      map_add' := fun χ ψ => by simp [TensorProduct.tmul_add] }
  map_add' v w := by
    apply AddMonoidHom.ext
    intro χ
    simp only [map_add]
    rfl
  map_smul' r v := by
    apply AddMonoidHom.ext
    intro χ
    simp only [map_smul, RingHom.id_apply]
    rfl

omit [NumberField F] in
/-- Character pairing with the projected vector agrees with the pairing against the
restricted character of the maximal split torus. -/
theorem realParameterPairing_splitDual (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (x : RealCharacterParameter F (𝓕.P Q)) (v : V 𝓕.T) :
    realParameterPairing F (𝓕.P Q) x (𝓕.splitDual Q v) =
      pair 𝓕.T (𝓕.chamberEmbedding Q x) v := by
  induction x using TensorProduct.inductionOn with
  | tmul a χ =>
    rw [realParameterPairing_tmul, show a ⊗ₜ[ℤ] χ = a • ((1 : ℝ) ⊗ₜ[ℤ] χ) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, LinearMap.smul_apply]
    rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The coroot `α̌_Q ∈ 𝔞_Q^G` of `α ∈ Δ_Q`: the projection to `𝔞_Q` of the coroot `α̌` of the
simple root of `Δ_0` restricting to `α`. The `α̌_Q` form a basis of `𝔞_Q^G` and generate the
lattice `L_Q`. -/
def relativeCoroot (Q : StandardIndex F G 𝓕.i 𝓕.ν) (α : 𝓕.relativeSimpleRoots Q) :
    RealCharacterDual F (𝓕.P Q) :=
  𝓕.splitDual Q (𝓕.coroots.realCoroot ⟨α, 𝓕.mem_relativeRoots_of_mem_relativeSimpleRoots Q α⟩)

/-- `⟨λ, α̌_Q⟩` for `λ ∈ 𝔞_{Q,ℂ}^*`. -/
def corootValue (Q : StandardIndex F G 𝓕.i 𝓕.ν) (lam : ComplexCharacterParameter F (𝓕.P Q))
    (α : 𝓕.relativeSimpleRoots Q) : ℂ :=
  complexParameterPairing F (𝓕.P Q) lam (𝓕.relativeCoroot Q α)

/-- The coordinate `ϖ_α(T)` of `T_Q = ∑_{α ∈ Δ_Q} ϖ_α(T) α̌_Q` (for `T ∈ 𝔞_0^G`), with the
fundamental weight `ϖ_α ∈ Δ̂_0` of `α`. -/
def weightCoordinate (Q : StandardIndex F G 𝓕.i 𝓕.ν) (Tp : V 𝓕.T) (α : 𝓕.relativeSimpleRoots Q) :
    ℝ :=
  ArthurRelative.weight 𝓕.connectedReductive 𝓕.maximalSplit 𝓕.ν 𝓕.coroots
    (ArthurTruncation.simpleFinset 𝓕.ν 𝓕.connectedReductive 𝓕.maximalSplit :
      Set (characterLattice 𝓕.T)) α Tp

/-! ### Unitary exponent and polynomial data and the regularized integrals -/

/-- **Finite unitary exponent and polynomial data** on `𝔞_Q^G`: a finite set of exponents
`λ ∈ 𝔞_{Q,ℂ}^*` with `Re λ = 0` and, for each, a polynomial in the coroot coordinates `c` of
`X = ∑_{α ∈ Δ_Q} c_α α̌_Q`, describing the exponential polynomial
`X ↦ ∑_λ e^{⟨λ, X⟩} P_λ(c)` (`UnitaryPairingExpansion.eval`). -/
structure UnitaryPairingExpansion (Q : StandardIndex F G 𝓕.i 𝓕.ν) where
  exponents : Finset (ComplexCharacterParameter F (𝓕.P Q))
  coefficient : ComplexCharacterParameter F (𝓕.P Q) → MvPolynomial (𝓕.relativeSimpleRoots Q) ℂ
  unitary : ∀ lam ∈ exponents, parameterRealPart F (𝓕.P Q) lam = 0

variable {𝓕}

/-- The value `∑_λ e^{∑_α c_α ⟨λ, α̌_Q⟩} P_λ(c)` of the data at `X = ∑_α c_α α̌_Q`. -/
def UnitaryPairingExpansion.eval {Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (e : 𝓕.UnitaryPairingExpansion Q) (c : 𝓕.relativeSimpleRoots Q → ℝ) : ℂ :=
  ∑ lam ∈ e.exponents, Complex.exp (∑ α, (c α : ℂ) * 𝓕.corootValue Q lam α) *
    MvPolynomial.eval (fun α => (c α : ℂ)) (e.coefficient lam)

/-- **The nonvanishing test for the supplied exponents**: every coroot value `⟨λ, α̌_Q⟩` of every
exponent `λ` listed in `e` is nonzero, so `θ_Q(λ) = ∏_{α ∈ Δ_Q} ⟨λ, α̌_Q⟩ ≠ 0` and the closed formula
of the regularized integral divides by no zero. It tests only the finite list of this presentation
of one slice; the parameter region of Delorme's Theorem 7.1 (i), which concerns all central
translates and the fixed labels of (7.12), is described by `genericParameterRegion`. -/
def UnitaryPairingExpansion.IsRegular {Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (e : 𝓕.UnitaryPairingExpansion Q) : Prop :=
  ∀ lam ∈ e.exponents, ∀ α, 𝓕.corootValue Q lam α ≠ 0

/-- **The regularized integral** of the data over `𝔞^G_{Q,−}(T) = T_Q + (negative coroot cone)`, in
coroot coordinates `X = ∑_α (ϖ_α(T) + c_α) α̌_Q`, `c ≤ 0`:
`∑_λ e^{⟨λ, T_Q⟩} ∫*_{c ≤ 0} e^{∑_α c_α ⟨λ, α̌_Q⟩} P_λ(ϖ(T) + c) dc`. Delorme's `r^T_Q` (7.9) is
`C_Q` times this value. -/
def UnitaryPairingExpansion.regularizedConeIntegral {Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (e : 𝓕.UnitaryPairingExpansion Q) (Tp : V 𝓕.T) : ℂ :=
  ∑ lam ∈ e.exponents,
    Complex.exp (∑ α, (𝓕.weightCoordinate Q Tp α : ℂ) * 𝓕.corootValue Q lam α) *
      negativeOrthantRegularizedIntegral (𝓕.corootValue Q lam)
        (polynomialShift (𝓕.weightCoordinate Q Tp) (e.coefficient lam))

variable (𝓕)

/-- **The normalized pairing (3.7)** `(f, g)^X_Q = e^{−2ρ_Q(X)} ∫_{K × M_Q(F) \ M_Q(𝔸)^1}
f(x m k) conj g(x m k)` at `x = exp_Q X ∈ P_Q(𝔸)`, with the integrand
`squareIntegrablePairingIntegrand` and the measure `squareIntegrablePairingMeasure` of
`AdelicTemperedVanishingReduction` and `e^{−2ρ_Q(X)} = (x^{ρ_Q})^{−2}` (`halfModulus`). -/
def normalizedPairing (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    (x : AdelicGroupPoints F (𝓕.P Q)) (f g : AdelicGroupPoints F G → ℂ) : ℂ :=
  (𝓕.halfModulus Q x ^ 2)⁻¹ *
    ∫ w, 𝓕.squareIntegrablePairingIntegrand K Q x f g w ∂𝓕.squareIntegrablePairingMeasure K hKc Q

/-! ### Delorme's extension of the pairing and the relation to the weak constant terms -/

/-- `P_Q(𝔸) K = G(𝔸)` for every standard index `Q`, from `P_∅(𝔸) K = G(𝔸)` and `P_∅ ⊆ P_Q`. -/
theorem isIwasawaCompact_index (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K)
    (Q : StandardIndex F G 𝓕.i 𝓕.ν) : IsIwasawaCompact (𝓕.p Q) K := by
  have hle := (𝓕.le_iff_range_le 𝓕.bot Q).mp (Set.empty_subset Q.1)
  have hRange : Set.range (map F (𝓕.P 𝓕.bot) G (𝓕.p 𝓕.bot)) ⊆
      Set.range (map F (𝓕.P Q) G (𝓕.p Q)) := by
    change (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (𝓕.p 𝓕.bot)) :
        Set (AdelicGroupPoints F G)) ⊆
      (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (𝓕.p Q)) :
        Set (AdelicGroupPoints F G))
    exact hle _
  refine ⟨hK.isCompact, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.range_mul]
  exact Set.mul_subset_mul_right hRange

attribute [local instance] isClosedImmersion_p

/-- **Delorme's decomposition of the first argument of `p_Q`** (Delorme 2023, p.15, between (3.7)
and Remark 3.9, with the twists `φ_λ` of p.9): `f = ∑_{λ ∈ s} (φ λ)_λ + f₁`, where every `φ λ`
lies in `A^2_Q` (`IsSquareIntegrableInducedForm` for `P_Q = M_Q U_Q`, `K`, `rho`), its twist
`(φ λ)_λ(g) = φ λ (g) m_Q(g)^λ` is `hKQ.parameterTwist (φ λ) λ`, and the remainder
`f₁ = f − ∑_{λ ∈ s} (φ λ)_λ` satisfies the condition `IsSquareIntegrableOrthogonal` defining
`𝒜^{temp,c}_Q(G)`. Delorme's extended pairing of `f` with `ψ` is the pairing of the
square-integrable part `∑_{λ ∈ s} (φ λ)_λ` alone. -/
def IsSquareIntegrableTwistDecomposition {d N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) {Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (hKQ : IsIwasawaCompact (𝓕.p Q) K) (f : AdelicGroupPoints F G → ℂ)
    (s : Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (φ : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) : Prop :=
  (∀ lam ∈ s, IsSquareIntegrableInducedForm K hKQ.isCompact rho hsmooth hcalc (𝓕.p Q) (𝓕.iU Q)
      (𝓕.l Q) (φ lam)) ∧
    𝓕.IsSquareIntegrableOrthogonal K hKQ.isCompact rho hsmooth hcalc Q
      (f - ∑ lam ∈ s, hKQ.parameterTwist (φ lam) lam)

/-- **The relation of the data to a sum of normalized pairings**: for every `x ∈ 𝔄_Q` with
`H_Q(x) = ∑_α c_α α̌_Q ∈ 𝔞_Q^G`, the pairing integrand of every `u i`, `i ∈ s`, against `g` at
`x` is integrable, and `∑_{i ∈ s} (u i, g)^X_Q` (normalized pairings (3.7)) equals the value of
`e` at `c`. -/
def IsNormalizedPairingExpansion (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    {κ : Type*} (s : Finset κ) (u : κ → AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G → ℂ) (e : 𝓕.UnitaryPairingExpansion Q) : Prop :=
  ∀ x ∈ 𝓕.positiveSplitComponent Q, ∀ c : 𝓕.relativeSimpleRoots Q → ℝ,
    characterLog F (𝓕.P Q) x = ∑ α, c α • 𝓕.relativeCoroot Q α →
      (∀ i ∈ s, Integrable (𝓕.squareIntegrablePairingIntegrand K Q x (u i) g)
          (𝓕.squareIntegrablePairingMeasure K hKc Q)) ∧
        ∑ i ∈ s, 𝓕.normalizedPairing K hKc Q x (u i) g = e.eval c

/-- **The data `e Q` describe Delorme's extended pairings of the weak constant terms**: for every
standard `Q` there are weak constant terms `E_Q = E^w_Q` and `Φ_Q = Φ^w_Q` (`IsWeakConstantTerm`,
Delorme's Definition 3.7, for the archimedean part of `K`) and a decomposition
`E_Q = ∑_{λ ∈ s} (φ λ)_λ + f₁` as in `IsSquareIntegrableTwistDecomposition`, such that `e Q`
describes `∑_{λ ∈ s}` of the normalized pairings on `𝔞_Q^G` of the central translates
`((φ λ)_λ)^Z` and `(Φ_Q)^Z`. The remainder `f₁` does not enter the pairing. -/
def IsWeakConstantTermPairingExpansion {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (rho : MatrixRepresentation G (Fin N))
    (hK : IsIwasawaCompact (𝓕.p 𝓕.bot) K) (z : 𝓕.positiveSplitComponent 𝓕.top)
    (E Φ : AdelicGroupPoints F G → ℂ)
    (e : ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.UnitaryPairingExpansion Q) : Prop :=
  ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, ∃ (EQ ΦQ : AdelicGroupPoints F G → ℂ)
    (s : Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (φ : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ),
    𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q E EQ ∧
      𝓕.IsWeakConstantTerm hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q Φ ΦQ ∧
      𝓕.IsSquareIntegrableTwistDecomposition rho hsmooth hcalc (𝓕.isIwasawaCompact_index hK Q)
        EQ s φ ∧
      𝓕.IsNormalizedPairingExpansion K hK.isCompact Q s
        (fun lam => 𝓕.centralTranslate z ((𝓕.isIwasawaCompact_index hK Q).parameterTwist
          (φ lam) lam))
        (𝓕.centralTranslate z ΦQ) (e Q)

/-- The expansion with no exponents, describing the zero function. -/
def UnitaryPairingExpansion.zero (Q : StandardIndex F G 𝓕.i 𝓕.ν) : 𝓕.UnitaryPairingExpansion Q where
  exponents := ∅
  coefficient := fun _ => 0
  unitary := fun _ h => absurd h (Finset.notMem_empty _)

/-- With no square-integrable pieces, the relation holds for the zero expansion: this is the case
of a first argument lying entirely in the orthogonal complement (for instance an Eisenstein series
induced from a proper parabolic, at `Q = G`, by Delorme's (4.6)). -/
theorem isNormalizedPairingExpansion_empty (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (Q : StandardIndex F G 𝓕.i 𝓕.ν)
    {κ : Type*} (u : κ → AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G → ℂ) :
    𝓕.IsNormalizedPairingExpansion K hKc Q ∅ u g (UnitaryPairingExpansion.zero 𝓕 Q) := by
  intro x _ c _
  refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
  simp [UnitaryPairingExpansion.eval, UnitaryPairingExpansion.zero]

/-! ### The generic parameter region of fixed exponent labels -/

/-- **Affine exponent labels** from `𝔞_{P,ℂ}^*` to `𝔞_{Q,ℂ}^*`: finitely many maps
`λ ↦ A_k λ + b_k`, `k : Fin size`, with `A_k` complex linear. For `E(λ) = E_P(·, φ, λ)` and a
tempered `Φ`, the labels of the `Q`-term of Delorme's (7.12) are `λ ↦ sλ − μ` for `s ∈ W(P|Q)` and
the exponents `μ ∈ ℰ_Q(Φ^w_Q)` of `Φ^w_Q`; they do not depend on the central translate. -/
structure AffineExponentLabels (P Q : StandardIndex F G 𝓕.i 𝓕.ν) where
  size : ℕ
  linear : Fin size →
    (ComplexCharacterParameter F (𝓕.P P) →ₗ[ℂ] ComplexCharacterParameter F (𝓕.P Q))
  offset : Fin size → ComplexCharacterParameter F (𝓕.P Q)

variable {𝓕}

/-- The label `A_k λ + b_k` of index `k` at the parameter `λ`. -/
def AffineExponentLabels.label {P Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (L : 𝓕.AffineExponentLabels P Q) (k : Fin L.size)
    (lam : ComplexCharacterParameter F (𝓕.P P)) : ComplexCharacterParameter F (𝓕.P Q) :=
  L.linear k lam + L.offset k

omit [NumberField F] in
/-- The coroot values of a label are affine functions of the parameter. -/
theorem AffineExponentLabels.corootValue_label {P Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (L : 𝓕.AffineExponentLabels P Q) (k : Fin L.size)
    (lam : ComplexCharacterParameter F (𝓕.P P)) (α : 𝓕.relativeSimpleRoots Q) :
    𝓕.corootValue Q (L.label k lam) α =
      complexParameterPairing F (𝓕.P Q) (L.linear k lam) (𝓕.relativeCoroot Q α) +
        𝓕.corootValue Q (L.offset k) α := by
  simp only [AffineExponentLabels.label, StandardParabolicFamily.corootValue, map_add,
    LinearMap.add_apply]

/-- **The exponents of the data are among the labels at `λ`**: every exponent of `e` is
`A_k λ + b_k` for some label `k` of `L`. -/
def UnitaryPairingExpansion.IsLabelledBy {P Q : StandardIndex F G 𝓕.i 𝓕.ν}
    (e : 𝓕.UnitaryPairingExpansion Q) (L : 𝓕.AffineExponentLabels P Q)
    (lam : ComplexCharacterParameter F (𝓕.P P)) : Prop :=
  ∀ lam' ∈ e.exponents, ∃ k, L.label k lam = lam'

variable (𝓕)

/-- **The generic parameter region of fixed labels**: the `λ ∈ 𝔞_{P,ℂ}^*` such that, for every
standard `Q` and every label `k` of `L Q`, `θ_Q(A_k λ + b_k) ≠ 0`, that is, every coroot value
`⟨A_k λ + b_k, α̌_Q⟩`, `α ∈ Δ_Q`, is nonzero. Every label is tested, whatever the coefficients of
the data on a particular slice. For Delorme's labels `sλ − μ` this is the region
`θ_Q(sλ − μ) ≠ 0` which, by (7.12), lies in the set `ℋ^c` of Theorem 7.1 (i) (on `i𝔞_P^*`). -/
def genericParameterRegion (P : StandardIndex F G 𝓕.i 𝓕.ν)
    (L : ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.AffineExponentLabels P Q) :
    Set (ComplexCharacterParameter F (𝓕.P P)) :=
  {lam | ∀ Q (k : Fin (L Q).size) α, 𝓕.corootValue Q ((L Q).label k lam) α ≠ 0}

variable {𝓕}

omit [NumberField F] in
/-- Data whose exponents are among the labels at a parameter of the generic region pass the
nonvanishing test `IsRegular`. -/
theorem UnitaryPairingExpansion.isRegular_of_mem_genericParameterRegion
    {P : StandardIndex F G 𝓕.i 𝓕.ν}
    {L : ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.AffineExponentLabels P Q}
    {lam : ComplexCharacterParameter F (𝓕.P P)} (hlam : lam ∈ 𝓕.genericParameterRegion P L)
    {Q : StandardIndex F G 𝓕.i 𝓕.ν} (e : 𝓕.UnitaryPairingExpansion Q)
    (he : e.IsLabelledBy (L Q) lam) : e.IsRegular := by
  intro lam' hlam' α
  obtain ⟨k, rfl⟩ := he lam' hlam'
  exact hlam Q k α

variable (𝓕)

/-- **`ω^T_{P_0} = ∑_{Q ∈ 𝒫_st} r^T_Q`** (Delorme 2023, Theorem 7.1, with (7.8)–(7.12)): the finite
sum over the standard indices `Q` of `vol Q` times the regularized cone integral of `e Q`. Delorme's
normalization is `vol Q = C_Q = vol(𝔞_Q^G / L_Q)`. -/
def regularizedPairing (vol : StandardIndex F G 𝓕.i 𝓕.ν → ℝ)
    (e : ∀ Q : StandardIndex F G 𝓕.i 𝓕.ν, 𝓕.UnitaryPairingExpansion Q) (Tp : V 𝓕.T) : ℂ :=
  ∑ᶠ Q : StandardIndex F G 𝓕.i 𝓕.ν, (vol Q : ℂ) * (e Q).regularizedConeIntegral Tp

end StandardParabolicFamily

end Langlands.Global
