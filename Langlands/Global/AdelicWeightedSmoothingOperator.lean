import Langlands.Global.AdelicWeightedConvolutionDerivativeEstimate
import Langlands.Global.AdelicWeightedChamberLocalIntegrability
import Langlands.Automorphic.GroupSchemeUniformGrowthOperators
import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction

/-! # Weighted right convolution into the uniform-growth Fréchet space -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints InfiniteAdelicGroupPoints RepresentationGrowth
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {n d : ℕ} (rho : GroupScheme.MatrixRepresentation G (Fin n))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)

local notation "A" => AdelicGroupPoints F G
local notation "A_f" => FiniteAdelicGroupPoints F G
local notation "ΓG" => rationalSubgroup F G
local notation "μG" => (Measure.haar : Measure A)
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth

/-- Squared integral of an ambient function in the weighted parabolic fundamental domain. -/
def chamberSquareIntegral (ell : RealCharacterDual F P → ℝ)
    (S : Set (RealCharacterDual F P)) (f : A → ℂ) : ℝ≥0∞ :=
  ∫⁻ g in LeftCosetSpace.fundamentalDomain (parabolicPrincipalSubgroup F p)
      (isDiscrete_parabolicPrincipalSubgroup F p),
      ‖f g‖ₑ ^ (2 : ℕ) * chamberDensity F p hK ell S g ∂μG

private theorem rightConvolution_invariant {h f : A → ℂ}
    (hf : ∀ r : ΓG, ∀ x, f (r.val * x) = f x) (r : ΓG) (x : A) :
    rightConvolution F G h f (r.val * x) = rightConvolution F G h f x := by
  simp only [rightConvolution, mul_assoc, hf]

private theorem rightConvolution_fixed {h f : A → ℂ} (L : Subgroup A_f)
    (hL : ∀ l ∈ L, ∀ x, h (ofFinite F G l * x) = h x) (l : A_f) (hl : l ∈ L) (x : A) :
    rightConvolution F G h f (x * ofFinite F G l) = rightConvolution F G h f x := by
  rw [rightConvolution_eq_integral_leftKernel, rightConvolution_eq_integral_leftKernel]
  simp only [mul_inv_rev, ← map_inv, mul_assoc, hL _ (L.inv_mem hl)]

private def rationalSmoothRightConvolution {h f : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (hf : Measurable f) (hfi : LocallyIntegrable f μG)
    (hinv : ∀ r : ΓG, ∀ x, f (r.val * x) = f x) : FinitePlotSmoothRationalFunctions F G := by
  have hs := (adelicRightConvolutionDifferentiation F G d hsmooth h f hh hf hfi).2.1
  let g : ContinuousRationalFunctions F G :=
    ⟨⟨rightConvolution F G h f, fun r x => rightConvolution_invariant hinv ⟨_, ⟨r, rfl⟩⟩ x⟩, hs.1⟩
  let U := hs.2.2.choose
  refine ⟨g, (mem_infinitePlotSmoothSubrepresentation F G g).mpr hs.2.1,
    ⟨⟨U, hs.2.2.choose_spec.1⟩, ?_⟩⟩
  intro u
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hs.2.2.choose_spec.2 u u.property x

private theorem derivative_rationalSmoothRightConvolution {h f : A → ℂ}
    (hh : IsAdelicTestFunction F G h) (hf : Measurable f) (hfi : LocallyIntegrable f μG)
    (hinv : ∀ r : ΓG, ∀ x, f (r.val * x) = f x) (a : UEA) (x : A) :
    evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a
        (rationalSmoothRightConvolution hsmooth hh hf hfi hinv)).val x =
      (plotSmoothEnvelopingAction F G hsmooth hcalc a
        (rightConvolutionSmoothSlice hsmooth h f hh hf hfi (finite F G x))).val (infinite F G x) := by
  let g := rationalSmoothRightConvolution hsmooth hh hf hfi hinv
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) := Module.addCommMonoidToAddCommGroup ℂ
  have eq := finitePlotSmoothSlice_envelopingAction F G hsmooth hcalc a (finite F G x) g
  have he := congrArg (fun s : InfinitePlotSmoothFunctions F G => s.val (infinite F G x)) eq
  change evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a g).val
    (pair F G (infinite F G x) (finite F G x)) = _ at he
  rw [pair_projections] at he
  exact he

/-- Given polynomially controlled rational representatives and a bound for the weighted norm
of the input on the enlarged region, right convolution defines a continuous linear map into
all sufficiently large uniform-growth spaces at a fixed permitted finite level. -/
def AdelicWeightedSmoothingOperatorStatement : Prop :=
  ∀ (hn : 0 < n) (hrho : GroupScheme.IsClosedSubgroup rho)
    (ell : RealCharacterDual F P → ℝ), Continuous ell →
  ∀ (W r : ℝ), 0 < W → 0 ≤ r →
  (∀ g, Real.exp (ell (hK.height g)) ≤ W * adelicHeight F G rho g ^ r) →
  ∀ (Y : Set A) (M t : ℝ), 0 < M → 0 ≤ t →
  (∀ x : A, ∃ q : ΓG, q.val * x ∈ Y ∧
    adelicHeight F G rho (q.val * x) ≤ M * adelicHeight F G rho x ^ t) →
  ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ R ≥ R₀,
  ∀ (Kf : Set A_f), IsCompact Kf → MapsTo (finite F G) Y Kf →
  ∀ (S : Set (RealCharacterDual F P)), IsOpen S → MapsTo hK.height Y S →
  ∀ (h : A → ℂ), IsAdelicTestFunction F G h →
  (∀ x ∈ Y, ∀ a ∈ tsupport h, hK.height (x * a) ∈ S) →
  ∀ (L : Subgroup A_f), (∀ l ∈ L, ∀ x, h (ofFinite F G l * x) = h x) →
  ∀ (B : Type u) [NormedAddCommGroup B] [NormedSpace ℂ B] (rep : B →ₗ[ℂ] (A → ℂ)),
  (∀ b, Measurable (rep b)) → (∀ b (q : ΓG) x, rep b (q.val * x) = rep b x) →
  ∀ D : ℝ, 0 ≤ D →
  (∀ b, chamberSquareIntegral hK ell S (rep b) < ∞ ∧
    Real.sqrt (chamberSquareIntegral hK ell S (rep b)).toReal ≤ D * ‖b‖) →
  ∃ T : B →L[ℂ] UniformGrowthFrechetSpace F G rho hsmooth hcalc hn hrho R L,
    ∀ b x, UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hn hrho R L (T b) x =
      rightConvolution F G h (rep b) x

theorem adelicWeightedSmoothingOperator : AdelicWeightedSmoothingOperatorStatement hK rho hsmooth hcalc := by
  intro hn hrho ell hell W r hW hr hweight Y M t hM ht hY
  obtain ⟨E, hE, hbound⟩ := adelicWeightedConvolutionDerivativeEstimate hK rho hsmooth hcalc
    hn hrho ell hell W r hW hr hweight
  refine ⟨t * E, mul_nonneg ht hE, ?_⟩
  intro R hR Kf hKf hfin S hS hSY h hh hSupp L hL B _ _ rep hrep hInv D hD hnorm
  let : MeasurableSpace (RealCharacterDual F P) := borel _
  let : BorelSpace (RealCharacterDual F P) := ⟨rfl⟩
  let : AddCommGroup (FinitePlotSmoothRationalFunctions F G) := Module.addCommMonoidToAddCommGroup ℂ
  have hcover (x : A) : ∃ q : ΓG, hK.height (q.val * x) ∈ S := by
    obtain ⟨q, hq, _⟩ := hY x
    exact ⟨q, hSY hq⟩
  have hloc (b : B) : LocallyIntegrable (rep b) μG :=
    weightedChamberLocalIntegrability hK ell hell S hS hcover (rep b) (hrep b)
      (hInv b) (hnorm b).1
  let out (b : B) := rationalSmoothRightConvolution hsmooth hh (hrep b) (hloc b) (hInv b)
  have hFixed (b : B) : IsFixedByFiniteSubgroup F G L (out b) := by
    intro l hl
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact rightConvolution_fixed (f := rep b) L hL l hl x
  let C₀ : ℝ := (n : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  have hC₀ : 0 < C₀ := pow_pos (by exact_mod_cast hn) _
  let H := adelicHeight F G rho
  let N := adelicSourceNorm F G rho
  have hH (x : A) : 1 ≤ H x := one_le_adelicHeight F G rho hn x
  have hdiff (a : UEA) : ∃ c : ℝ, 0 ≤ c ∧ ∀ b x,
      ‖evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a (out b)).val x‖ ≤
        c * ‖b‖ * N x ^ R := by
    obtain ⟨C, hC, hCa⟩ := hbound Kf hKf h hh a
    refine ⟨C * M ^ E * D * C₀ ^ R, by positivity, fun b x => ?_⟩
    obtain ⟨q, hq, hqx⟩ := hY x
    let y := q.val * x
    have hy : y ∈ Y := hq
    have hInvOut : evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a (out b)).val y =
        evaluate F G (adelicEnvelopingAction F G hsmooth hcalc a (out b)).val x := by
      obtain ⟨q₀, hq₀⟩ := q.property
      change rational F G q₀ = q.val at hq₀
      unfold y
      rw [← hq₀, evaluate_rational_mul]
    rw [← hInvOut, show out b = _ from rfl,
      derivative_rationalSmoothRightConvolution]
    have hybound := hCa S hS.measurableSet y (hfin hy) (hSupp y hy) (rep b) (hrep b) (hloc b)
      (fun q x => hInv b ⟨q.val, parabolicPrincipalSubgroup_le F p q.property⟩ x) (hnorm b).1
    refine hybound.trans ?_
    have hxy : H y ^ E ≤ M ^ E * H x ^ R := calc
      _ ≤ (M * H x ^ t) ^ E := Real.rpow_le_rpow (zero_le_one.trans (hH y)) hqx hE
      _ = M ^ E * H x ^ (t * E) := by
        rw [Real.mul_rpow hM.le (Real.rpow_nonneg (zero_le_one.trans (hH x)) t),
          ← Real.rpow_mul (zero_le_one.trans (hH x))]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hH x) hR)
        (Real.rpow_nonneg hM.le _)
    calc
      _ ≤ C * (M ^ E * H x ^ R) * (D * ‖b‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hxy hC) (hnorm b).2 (Real.sqrt_nonneg _)
          (mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hM.le _)
            (Real.rpow_nonneg (zero_le_one.trans (hH x)) _)))
      _ = _ := by
        rw [show H x = C₀ * N x from adelicHeight_eq_scalar_mul_sourceNorm F G rho x,
          Real.mul_rpow hC₀.le (adelicSourceNorm_pos F G rho hn x).le]
        ring
  let V := UniformGrowthFrechetSpace F G rho hsmooth hcalc hn hrho R L
  let v (b : B) : V := ⟨out b, hFixed b, fun a => by
    obtain ⟨c, _, hc⟩ := hdiff a
    exact ⟨c * ‖b‖, hc b⟩⟩
  have hv (b : B) (x : A) : UniformGrowthFrechetSpace.toFun F G rho hsmooth hcalc hn hrho R L (v b) x =
      rightConvolution F G h (rep b) x := rfl
  let T : B →ₗ[ℂ] V :=
    { toFun := v
      map_add' := by
        intro b₁ b₂
        apply toFun_injective F G rho hsmooth hcalc hn hrho R L
        funext x
        change rightConvolution F G h (rep (b₁ + b₂)) x =
          rightConvolution F G h (rep b₁) x + rightConvolution F G h (rep b₂) x
        simp only [rightConvolution, map_add, Pi.add_apply, mul_add]
        exact integral_add
          ((adelicRightConvolutionDifferentiation F G d hsmooth h (rep b₁) hh (hrep b₁) (hloc b₁)).1 x)
          ((adelicRightConvolutionDifferentiation F G d hsmooth h (rep b₂) hh (hrep b₂) (hloc b₂)).1 x)
      map_smul' := by
        intro z b
        apply toFun_injective F G rho hsmooth hcalc hn hrho R L
        funext x
        change rightConvolution F G h (rep (z • b)) x = z * rightConvolution F G h (rep b) x
        simp only [rightConvolution, map_smul, Pi.smul_apply, smul_eq_mul,
          mul_left_comm (h _) z, integral_const_mul] }
  refine ⟨⟨T, ?_⟩, hv⟩
  apply UniformGrowthFrechetSpace.continuous_of_weightedDerivative
  intro a
  obtain ⟨c, hc, ha⟩ := hdiff a
  let Dₐ := (weightedDerivativeLinearMap F G rho hsmooth hcalc hn hrho R L a).comp T
  have hnormD (b : B) : ‖Dₐ b‖ ≤ c * ‖b‖ := by
    apply lp.norm_le_of_forall_le (mul_nonneg hc (norm_nonneg _))
    intro x
    change ‖weightedDerivative F G rho hsmooth hcalc hn hrho R L a (v b) x‖ ≤ _
    have hpos : 0 < N x ^ R := Real.rpow_pos_of_pos (adelicSourceNorm_pos F G rho hn x) _
    rw [weightedDerivative_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, ← div_eq_mul_inv, div_le_iff₀ hpos]
    exact ha b x
  exact (Dₐ.mkContinuous c hnormD).continuous

end Langlands.Global.WeightedSiegel
