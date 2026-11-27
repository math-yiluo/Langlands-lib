import Langlands.Global.AdelicSiegelConstantTermGrowth
import Langlands.Global.AdelicSiegelHalfModulus
import Langlands.Global.AdelicSiegelSplitRays
import Langlands.Global.AdelicExponentRayBound
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof

/-! # Subunitarity of normalized exponents on the Siegel split rays -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors RepresentationGrowth

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "P" => fam.P J
local notation "Torus" => PositiveRealTorus.intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "pG" => map F P G (fam.p J)
local notation "H" => adelicHeight F G rho

/-- Logarithmic Siegel chamber growth implies the half-modulus ray bound used to test
normalized exponents, whenever all the powers of the split ray lie in that chamber. -/
theorem hasRayGrowth_of_siegelChamberGrowth
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    (hN : 0 < N) {f : A → ℂ} (hf : fam.HasSiegelChamberGrowth j rho f)
    (r : Torus) (t : ℝ≥0ˣ)
    (hr : ∀ n : ℕ, r ^ n ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t)
    (a : fam.positiveSplitComponent J) (ha : pG a.val = aG r) :
    ∀ g, ∃ (C : ℝ) (degree : ℕ), ∀ n : ℕ,
      ‖f ((pG a.val) ^ n * g)‖ ≤ C * ‖fam.halfModulus J a.val‖ ^ n * (1 + (n : ℝ)) ^ degree := by
  intro g
  obtain ⟨m, C, hC, hBound⟩ := hf t {g} isCompact_singleton
  let L := 1 + Real.log (H 1) + Real.log (H (aG r))
  have hH (y : A) : 1 ≤ H y := one_le_adelicHeight F G rho hN y
  have hlog (y : A) : 0 ≤ Real.log (H y) := Real.log_nonneg (hH y)
  have hL : 0 ≤ L := by dsimp only [L]; linarith [hlog 1, hlog (aG r)]
  have hPow (n : ℕ) : H ((aG r) ^ n) ≤ H 1 * H (aG r) ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (aG r), pow_succ (H (aG r)), ← mul_assoc]
      exact (adelicHeight_mul_le F G rho hN _ _).trans
        (mul_le_mul_of_nonneg_right ih (zero_le_one.trans (hH _)))
  have hSize (n : ℕ) : 1 + Real.log (H (aG (r ^ n))) ≤ L * (1 + (n : ℝ)) := by
    have hlogPow := Real.log_le_log (zero_lt_one.trans_le (hH ((aG r) ^ n))) (hPow n)
    rw [Real.log_mul (zero_lt_one.trans_le (hH 1)).ne'
      (pow_pos (zero_lt_one.trans_le (hH (aG r))) n).ne', Real.log_pow] at hlogPow
    rw [map_pow]
    dsimp only [L]
    nlinarith [hlogPow, hlog 1, hlog (aG r), mul_nonneg (Nat.cast_nonneg n) (hlog 1)]
  have hModPow (n : ℕ) : fam.halfModulus J (a ^ n).val = fam.halfModulus J a.val ^ n := by
    induction n with
    | zero => simp [halfModulus, parameterPower, characterLog_one]
    | succ n ih =>
      rw [pow_succ, Subgroup.coe_mul]
      change parameterPower F P (halfModulusParameter F P) ((a ^ n).val * a.val) = _
      rw [parameterPower_mul, pow_succ]
      exact congrArg (fun z => z * fam.halfModulus J a.val) ih
  refine ⟨C * L ^ m, m, fun n => ?_⟩
  have hShift : pG (a ^ n).val = aG (r ^ n) := by
    simp only [Subgroup.coe_pow, map_pow, ha]
  have hHalf := fam.halfModulus_eq_siegelSqrt_of_positiveSplitComponent hδ hsetup J
    (r ^ n) (a ^ n) hShift
  have hNorm := congrArg norm hHalf
  rw [hModPow, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hNorm
  calc
    ‖f ((pG a.val) ^ n * g)‖ = ‖f (aG (r ^ n) * g)‖ := by rw [ha, map_pow]
    _ ≤ C * Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j (r ^ n)) *
        (1 + Real.log (H (aG (r ^ n)))) ^ m := hBound _ (hr n) _ (Set.mem_singleton _)
    _ ≤ C * ‖fam.halfModulus J a.val‖ ^ n * (L * (1 + (n : ℝ))) ^ m := by
      rw [← hNorm]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [hlog (aG (r ^ n))]) (hSize n) _)
        (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
    _ = _ := by rw [mul_pow]; ring

/-- On a fundamental ray omitted from the Levi index, every nonzero normalized
exponent of a function with logarithmic Siegel chamber growth is subunitary. -/
theorem norm_parameterPower_le_one_on_siegelRay
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    {f : A → ℂ} {s : Finset (ComplexCharacterParameter F P)} {c : ComplexCharacterParameter F P → A → ℂ}
    (hDec : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J f s c)
    (hf : fam.HasSiegelChamberGrowth j rho f)
    (r : Torus) (t : ℝ≥0ˣ)
    (hr : ∀ n : ℕ, r ^ n ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t)
    (a : fam.positiveSplitComponent J) (ha : pG a.val = aG r)
    (lam : ComplexCharacterParameter F P) (hmem : lam ∈ s) (hne : c lam ≠ 0) :
    ‖parameterPower F P lam a.val‖ ≤ 1 :=
  fam.norm_parameterPower_le_one_of_ray_bound J hsmooth Kinf rho hDec a
    (fam.hasRayGrowth_of_siegelChamberGrowth j rho J hδ hsetup hN hf r t hr a ha) lam hmem hne

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- On a split ray with every nonnegative integer power in a weak Siegel chamber, a
logarithmic Siegel bound forces the norm of each nonzero normalized exponent to be at most one. -/
def AdelicSiegelExponentSubunitarityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    ∀ (fam : StandardParabolicFamily F G) (T₀ : CommGroupScheme (Spec (CommRingCat.of F)))
      (j : T₀ ⟶ fam.T),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
      (J : StandardIndex F G fam.i fam.ν),
    ∀ (f : AdelicGroupPoints F G → ℂ) (s : Finset (ComplexCharacterParameter F (fam.P J)))
      (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J f s c →
    fam.HasSiegelChamberGrowth j rho f →
    ∀ (r : intrinsicSubgroup F T₀) (t : ℝ≥0ˣ),
      (∀ n : ℕ, r ^ n ∈ weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν t) →
    ∀ (a : fam.positiveSplitComponent J),
      map F (fam.P J) G (fam.p J) a.val = positiveMap F G fam.T fam.i T₀ j r →
      ∀ lam ∈ s, c lam ≠ 0 → ‖parameterPower F (fam.P J) lam a.val‖ ≤ 1

theorem adelicSiegelExponentSubunitarity : AdelicSiegelExponentSubunitarityStatement := by
  intro F _ _ G _ _ _ fam T₀ j hsetup N d rho hN hsmooth Kinf J f s c hDec hGrowth r t hr a ha lam hlam hne
  exact fam.norm_parameterPower_le_one_on_siegelRay j rho J standardNestedHalfModulusCompatibility
    hsetup hN hsmooth Kinf hDec hGrowth r t hr a ha lam hlam hne

end Langlands.Global
