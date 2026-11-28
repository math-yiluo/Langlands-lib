import Langlands.Global.AdelicSiegelHalfModulus
import Langlands.Global.AdelicExponentRayInterpolation
import Langlands.Global.AdelicSiegelOrbitGrowth
import Langlands.Global.AdelicSiegelRayCoordinates
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.Global.SimpleRootBoxCompact

/-! # Uniform decay of strictly subunitary exponents along a Siegel ray -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus RepresentationGrowth
  Langlands.LinearAlgebra.RationalSpan

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "A" => AdelicGroupPoints F G
local notation "P(" J ")" => fam.P J
local notation "p(" J ")" => map F (fam.P J) G (fam.p J)
local notation "Param(" J ")" => ComplexCharacterParameter F (fam.P J)
local notation "χ(" J ")" => parameterPower F (fam.P J)

/-- Interpolation applies to an indexed family of sample points, even when the bound also
depends on the chosen index. Take an infimum over the indices with the same starting point. -/
private theorem exists_rayBound_of_indexed_samples (J : Idx)
    {lam : Param(J)} {f : A → ℂ} (hf : fam.HasUnnormalizedExponent J lam f)
    (a : fam.positiveSplitComponent J) {I : Type*} (x : I → A)
    (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hSample : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖f ((p(J) a.val) ^ n * x i)‖ ≤ C * B i)
    (q : ℝ) (hq : ‖χ(J) lam a.val‖ < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (i : I), ‖f ((p(J) a.val) ^ n * x i)‖ ≤ C * B i * q ^ n := by
  let levels (g : A) : Set ℝ := {r | ∃ i, x i = g ∧ B i = r}
  let b (g : A) := sInf (levels g)
  have hBelow (g : A) : BddBelow (levels g) :=
    ⟨0, fun _ ⟨i, _, hi⟩ => hi ▸ hB i⟩
  have hLevels (g : A) (hg : g ∈ Set.range x) : (levels g).Nonempty := by
    obtain ⟨i, rfl⟩ := hg
    exact ⟨B i, i, rfl, rfl⟩
  have hb (g : A) (hg : g ∈ Set.range x) : 0 ≤ b g :=
    le_csInf (hLevels g hg) fun _ ⟨i, _, hi⟩ => hi ▸ hB i
  have hSample' (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ Set.range x,
      ‖f ((p(J) a.val) ^ n * g)‖ ≤ C * b g := by
    obtain ⟨C, _, hC⟩ := hSample n
    let D := max 1 C
    have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
    refine ⟨D, hD.le, fun g hg => ?_⟩
    rw [mul_comm]
    apply (div_le_iff₀ hD).mp
    apply le_csInf (hLevels g hg)
    rintro _ ⟨i, rfl, rfl⟩
    exact (div_le_iff₀ hD).mpr
      ((hC i).trans (mul_comm D (B i) ▸ mul_le_mul_of_nonneg_right (le_max_right 1 C) (hB i)))
  obtain ⟨C, hC, hBound⟩ := fam.exists_rayBound_with_larger_rate J hf a hb hSample' q hq
  have hq₀ : 0 ≤ q := (norm_nonneg _).trans hq.le
  refine ⟨C, hC, fun n i => (hBound n _ ⟨i, rfl⟩).trans ?_⟩
  have hi : b (x i) ≤ B i := csInf_le (hBelow (x i)) ⟨i, rfl, rfl⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hC) (pow_nonneg hq₀ _)

variable {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "Torus" => intrinsicSubgroup F T₀
local notation "aG" => positiveMap F G fam.T fam.i T₀ j
local notation "δ" => siegelModulus F G fam.T fam.i fam.ν T₀ j
local notation "chamber" => weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
local notation "σ" => (fun a : Torus => 1 + Real.log (adelicHeight F G rho (aG a)))

/-- The square root of the Siegel modulus is multiplicative on the positive torus. -/
theorem siegelModulus_sqrt_mul
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (r a : Torus) :
    Real.sqrt (δ (r * a)) = Real.sqrt (δ r) * Real.sqrt (δ a) := by
  let q := map F T₀.toGrp (fam.P fam.bot)
    (CommGroupScheme.groupHom j ≫ fam.torus fam.bot ≫ fam.l fam.bot)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, ← fam.halfModulus_bot_eq_siegelSqrt hsetup (r * a),
    ← fam.halfModulus_bot_eq_siegelSqrt hsetup r, ← fam.halfModulus_bot_eq_siegelSqrt hsetup a]
  change χ(fam.bot) (halfModulusParameter F (fam.P fam.bot)) (q (r.val * a.val)) =
    χ(fam.bot) (halfModulusParameter F (fam.P fam.bot)) (q r.val) *
      χ(fam.bot) (halfModulusParameter F (fam.P fam.bot)) (q a.val)
  rw [map_mul, parameterPower_mul]

/-- A strictly subunitary component decays exponentially in the integer ray parameter
after division by the square root of the Siegel modulus. The coefficient and logarithmic
degree are uniform on the chamber of starting points and on compact right factors. -/
theorem exists_siegelRayBound_of_hasExponent
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N)
    (J : Idx) {lam : Param(J)} {f : A → ℂ} (hf : fam.HasExponent J lam f)
    (hGrowth : fam.HasSiegelChamberGrowth j rho f)
    (r : Torus) (hr : ∀ n : ℕ, r ^ n ∈ chamber 1)
    (b : fam.positiveSplitComponent J) (hb : p(J) b.val = aG r)
    (q : ℝ) (hq : ‖χ(J) lam b.val‖ < q)
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (n : ℕ) (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
      ‖f (aG (r ^ n * a) * w)‖ ≤
        C * Real.sqrt (δ (r ^ n * a)) * (σ a) ^ m * q ^ n := by
  obtain ⟨m, C, hC, hBound⟩ := hGrowth t Ω hΩ
  let I := {z : Torus × A // z.1 ∈ chamber t ∧ z.2 ∈ Ω}
  let x (i : I) := aG i.val.1 * i.val.2
  let B (i : I) := Real.sqrt (δ i.val.1) * (σ i.val.1) ^ m
  have hLog (a : Torus) : 0 ≤ Real.log (adelicHeight F G rho (aG a)) :=
    Real.log_nonneg (one_le_adelicHeight F G rho hN _)
  have hSig (a : Torus) : 0 ≤ σ a := by dsimp only; linarith [hLog a]
  have hLogMul (r a : Torus) : σ (r * a) ≤ σ r * σ a := by
    let H := adelicHeight F G rho
    have hH (g : A) : 0 < H g := zero_lt_one.trans_le (one_le_adelicHeight F G rho hN g)
    have h := Real.log_le_log (hH (aG r * aG a)) (adelicHeight_mul_le F G rho hN (aG r) (aG a))
    rw [Real.log_mul (hH _).ne' (hH _).ne'] at h
    simp only [map_mul]
    dsimp only [H] at h
    nlinarith [hLog r, hLog a, mul_nonneg (hLog r) (hLog a)]
  have hCh (n : ℕ) (i : I) : r ^ n * i.val.1 ∈ chamber t := by
    intro α hα
    have hn := hr n α hα
    have hi := i.property.1 α hα
    change 1 ≤ normCharacter F T₀ (j ≫ α) (r ^ n).val at hn
    change t ≤ normCharacter F T₀ (j ≫ α) i.val.1.val at hi
    change t ≤ normCharacter F T₀ (j ≫ α) ((r ^ n).val * i.val.1.val)
    rw [map_mul, mul_comm]
    exact hi.trans (le_mul_of_one_le_right' hn)
  have hArg (n : ℕ) (a : Torus) (w : A) :
      (p(J) b.val) ^ n * (aG a * w) = aG (r ^ n * a) * w := by
    rw [hb, map_mul, map_pow, mul_assoc]
  have hSamples (n : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ i : I, ‖f ((p(J) b.val) ^ n * x i)‖ ≤ D * B i := by
    refine ⟨C * Real.sqrt (δ (r ^ n)) * (σ (r ^ n)) ^ m,
      mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (pow_nonneg (hSig _) _), fun i => ?_⟩
    dsimp only [x, B]
    rw [hArg]
    calc
      ‖f (aG (r ^ n * i.val.1) * i.val.2)‖ ≤
          C * Real.sqrt (δ (r ^ n * i.val.1)) * (σ (r ^ n * i.val.1)) ^ m :=
        hBound _ (hCh n i) _ i.property.2
      _ ≤ C * Real.sqrt (δ (r ^ n * i.val.1)) * (σ (r ^ n) * σ i.val.1) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hSig _) (hLogMul _ _) _)
          (mul_nonneg hC (Real.sqrt_nonneg _))
      _ = _ := by rw [fam.siegelModulus_sqrt_mul j hsetup, mul_pow]; ring
  have hNorm := congrArg norm (fam.halfModulus_eq_siegelSqrt_of_positiveSplitComponent hδ hsetup J r b hb)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hNorm
  have hPos : 0 < Real.sqrt (δ r) := by
    rw [← hNorm]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hRate : ‖χ(J) (lam + halfModulusParameter F (fam.P J)) b.val‖ < q * Real.sqrt (δ r) := by
    rw [parameterPower_add, norm_mul]
    change ‖χ(J) lam b.val‖ * ‖fam.halfModulus J b.val‖ < _
    rw [hNorm]
    exact mul_lt_mul_of_pos_right hq hPos
  obtain ⟨D, hD, hTail⟩ := fam.exists_rayBound_of_indexed_samples J ((fam.hasExponent_iff J lam _).mp hf)
    b x B (fun i => mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hSig _) _)) hSamples _ hRate
  have hPow (n : ℕ) : Real.sqrt (δ (r ^ n)) = Real.sqrt (δ r) ^ n := by
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      apply Complex.ofReal_injective
      rw [Complex.ofReal_one, ← fam.halfModulus_bot_eq_siegelSqrt hsetup 1]
      simp [halfModulus, parameterPower, characterLog_one]
    | succ n ih => rw [pow_succ, fam.siegelModulus_sqrt_mul j hsetup, ih, pow_succ]
  refine ⟨m, D, hD, fun n a ha w hw => ?_⟩
  let i : I := ⟨(a, w), ha, hw⟩
  have h := hTail n i
  dsimp only [B, x, i] at h
  rw [hArg] at h
  rw [fam.siegelModulus_sqrt_mul j hsetup, hPow]
  calc
    _ ≤ D * (Real.sqrt (δ a) * (σ a) ^ m) * (q * Real.sqrt (δ r)) ^ n := h
    _ = _ := by rw [mul_pow]; ring

/-- A finite decomposition with strictly subunitary nonzero components has one
common exponential decay rate along the Siegel ray. -/
theorem exists_siegelRayDecay_of_exponentDecomposition
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N)
    (J : Idx) {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {f : A → ℂ} {s : Finset (Param(J))} {c : Param(J) → A → ℂ}
    (hDec : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J f s c)
    (hGrowth : fam.HasSiegelChamberGrowth j rho f)
    (r : Torus) (hr : ∀ n : ℕ, r ^ n ∈ chamber 1)
    (b : fam.positiveSplitComponent J) (hb : p(J) b.val = aG r)
    (hStrict : ∀ lam ∈ s, c lam ≠ 0 → ‖χ(J) lam b.val‖ < 1)
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ (q : ℝ), 0 < q ∧ q < 1 ∧ ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (n : ℕ) (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
        ‖f (aG (r ^ n * a) * w)‖ ≤
          C * Real.sqrt (δ (r ^ n * a)) * (σ a) ^ m * q ^ n := by
  classical
  let rate (lam : Param(J)) := if c lam = 0 then 0 else ‖χ(J) lam b.val‖
  let rates := insert (0 : ℝ) (s.image rate)
  obtain ⟨M, hMem, hMax⟩ := Finset.exists_max_image rates id ⟨0, Finset.mem_insert_self _ _⟩
  have hM₀ : 0 ≤ M := hMax 0 (Finset.mem_insert_self _ _)
  have hM₁ : M < 1 := by
    rcases Finset.mem_insert.mp hMem with rfl | h
    · exact zero_lt_one
    · obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp h
      by_cases hzero : c lam = 0
      · simpa only [rate, ite_eq_left hzero] using (zero_lt_one : (0 : ℝ) < 1)
      · simpa only [rate, ite_eq_right hzero] using hStrict lam hlam hzero
  let q := (M + 1) / 2
  have hq₀ : 0 < q := by dsimp only [q]; linarith
  have hq₁ : q < 1 := by dsimp only [q]; linarith
  have hqM : M < q := by dsimp only [q]; linarith
  have hComp (lam : Param(J)) : ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ (lam ∈ s →
      ∀ (n : ℕ) (a : Torus), a ∈ chamber t → ∀ w ∈ Ω,
        ‖c lam (aG (r ^ n * a) * w)‖ ≤
          C * Real.sqrt (δ (r ^ n * a)) * (σ a) ^ m * q ^ n) := by
    by_cases hlam : lam ∈ s
    · by_cases hzero : c lam = 0
      · exact ⟨0, 0, le_rfl, fun _ _ _ _ _ _ => by simp [hzero]⟩
      · have horbit := fam.exponentComponent_mem_splitComponentOrbitSpan J hDec.exponent lam hlam
        rw [← hDec.sum_eq] at horbit
        have hG := fam.hasSiegelChamberGrowth_of_mem_splitComponentOrbitSpan j rho hN J hGrowth horbit
        have hRate : ‖χ(J) lam b.val‖ < q := by
          have h := hMax (rate lam) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem rate hlam))
          exact (show ‖χ(J) lam b.val‖ ≤ M by simpa only [id, rate, ite_eq_right hzero] using h).trans_lt hqM
        obtain ⟨m, C, hC, hBound⟩ :=
          fam.exists_siegelRayBound_of_hasExponent j rho hδ hsetup hN J (hDec.exponent lam hlam)
            hG r hr b hb q hRate t Ω hΩ
        exact ⟨m, C, hC, fun _ => hBound⟩
    · exact ⟨0, 0, le_rfl, fun h => (hlam h).elim⟩
  choose m C hC hBound using hComp
  let d := s.sup m
  refine ⟨q, hq₀, hq₁, d, ∑ lam ∈ s, C lam, Finset.sum_nonneg (fun lam _ => hC lam), ?_⟩
  intro n a ha w hw
  have hσ : 1 ≤ σ a :=
    le_add_of_nonneg_right (Real.log_nonneg (one_le_adelicHeight F G rho hN _))
  rw [hDec.sum_eq, Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun lam hlam => (hBound lam hlam n a ha w hw).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hσ (Finset.le_sup (f := m) hlam))
      (mul_nonneg (hC lam) (Real.sqrt_nonneg _))) (pow_nonneg hq₀.le _)

local notation "Δ" => simpleRelativeRoots fam.i fam.ν
local notation "rootLog" => (fun (a : Torus) (β : characterLattice fam.T) =>
  characterLog F T₀.toGrp (Subtype.val a) (j ≫ β))

/-- In a fixed weak chamber the log height is bounded linearly by a common
nonnegative upper bound for the simple-root logarithms. -/
theorem exists_logHeight_le_of_simpleRoot_bounds
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N) (t : ℝ≥0ˣ) :
    ∃ V : ℝ, 0 ≤ V ∧ ∀ (a : Torus), a ∈ chamber t → ∀ L : ℝ, 0 ≤ L →
      (∀ β ∈ Δ, rootLog a β ≤ L) → σ a ≤ V * (1 + L) := by
  have hT₀ : IsSplitTorus T₀.toGrp := by
    obtain ⟨_, _, _, _, _, _, _, ⟨_, _, _, _, hT₀, _⟩, _⟩ := hsetup
    exact hT₀.isSplitSubtorus.1
  have hSpan : ratSpan ((fun β : characterLattice fam.T => j ≫ β) '' Δ) = ⊤ :=
    ratSpan_restrict_simpleRelativeRoots_eq_top relativeRootNegation relativeCharacterRootComplement
      fam.connectedReductive hsetup
  obtain ⟨P, D, hP, hD, hHeight⟩ := adelicPositiveTorusLogHeightBound
    (CommGroupScheme.groupHom j ≫ fam.i) rho _ hT₀ hSpan hN
  let T := Real.log ((t : ℝ≥0) : ℝ)
  let E := max 0 (-T)
  have hE : 0 ≤ E := le_max_left _ _
  let V := 1 + Real.log P + D * E + D
  have hV : 0 ≤ V := by
    dsimp only [V]
    linarith [Real.log_nonneg hP, mul_nonneg hD hE]
  refine ⟨V, hV, fun a ha L hL hUpper => ?_⟩
  have hLower := (mem_weakSimpleRootChamber_iff_log F T₀ fam.T j G fam.i fam.ν t a).mp ha
  have hAbs : ∀ χ ∈ (fun β : characterLattice fam.T => j ≫ β) '' Δ,
      |logNormHom F T₀ a.val χ| ≤ E + L := by
    rintro _ ⟨β, hβ, rfl⟩
    change |rootLog a β| ≤ E + L
    have hβL := hUpper β hβ
    have hβT : T ≤ rootLog a β := hLower β hβ
    have hET : -T ≤ E := le_max_right _ _
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hPosHeight : 0 < adelicHeight F G rho (aG a) :=
    zero_lt_one.trans_le (one_le_adelicHeight F G rho hN _)
  have hLogHeight := Real.log_le_log hPosHeight (hHeight a (E + L) (add_nonneg hE hL) hAbs)
  rw [Real.log_mul (zero_lt_one.trans_le hP).ne' (Real.exp_pos _).ne', Real.log_exp] at hLogHeight
  dsimp only [V]
  nlinarith [hLogHeight, Real.log_nonneg hP, mul_nonneg (Real.log_nonneg hP) hL,
    mul_nonneg (mul_nonneg hD hE) hL]

/-- The strictly subunitary exponent bound yields exponential decay in the distinguished
simple-root logarithm throughout the chamber. If all simple-root logs are at most `L`,
the extra factor is bounded by a polynomial in `1 + L`. -/
theorem exists_siegelChamberRayDecay_of_exponentDecomposition
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j) (hN : 0 < N)
    (J : Idx) {d : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)}
    {f : A → ℂ} {s : Finset (Param(J))} {c : Param(J) → A → ℂ}
    (hDec : fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J f s c)
    (hGrowth : fam.HasSiegelChamberGrowth j rho f)
    (α : Δ) (r : Torus) (hr : ∀ n : ℕ, r ^ n ∈ chamber 1)
    (hPos : 0 < rootLog r α.val)
    (hOff : ∀ β ∈ Δ, β ≠ α.val → rootLog r β = 0)
    (b : fam.positiveSplitComponent J) (hb : p(J) b.val = aG r)
    (hStrict : ∀ lam ∈ s, c lam ≠ 0 → ‖χ(J) lam b.val‖ < 1)
    (t : ℝ≥0ˣ) (Ω : Set A) (hΩ : IsCompact Ω) :
    ∃ (ε : ℝ), 0 < ε ∧ ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Torus), a ∈ chamber t → ∀ w ∈ Ω, ∀ L : ℝ, 0 ≤ L →
        (∀ β ∈ Δ, rootLog a β ≤ L) →
        ‖f (aG a * w)‖ ≤ C * Real.sqrt (δ a) * (1 + L) ^ m * Real.exp (-ε * rootLog a α.val) := by
  obtain ⟨q, hq, hq₁, m, C, hC, hRay⟩ :=
    fam.exists_siegelRayDecay_of_exponentDecomposition j rho hδ hsetup hN J hDec hGrowth
      r hr b hb hStrict t Ω hΩ
  obtain ⟨V, hV, hHeight⟩ := fam.exists_logHeight_le_of_simpleRoot_bounds j rho hsetup hN t
  let ε := -Real.log q / rootLog r α.val
  have hε : 0 < ε := div_pos (neg_pos.mpr (Real.log_neg hq hq₁)) hPos
  let T := Real.log ((t : ℝ≥0) : ℝ)
  let A₀ := Real.exp (ε * (T + rootLog r α.val))
  have hA₀ : 0 ≤ A₀ := (Real.exp_pos _).le
  refine ⟨ε, hε, m, C * V ^ m * A₀, mul_nonneg (mul_nonneg hC (pow_nonneg hV _)) hA₀,
    fun a ha w hw L hL hUpper => ?_⟩
  obtain ⟨n, a₀, he, ha₀, hle, _, _, hGeom⟩ :=
    exists_siegelChamber_rayFactor j fam.i fam.ν t α.property r hPos hOff a ha
  have hσ := hHeight a₀ ha₀ L hL (fun β hβ => (hle β hβ).trans (hUpper β hβ))
  have hσ₀ : 0 ≤ σ a₀ := by
    dsimp only
    linarith [Real.log_nonneg (one_le_adelicHeight F G rho hN (aG a₀))]
  have hRayPoint := hRay n a₀ ha₀ w hw
  rw [← he] at hRayPoint
  calc
    ‖f (aG a * w)‖ ≤ C * Real.sqrt (δ a) * (σ a₀) ^ m * q ^ n := hRayPoint
    _ ≤ C * Real.sqrt (δ a) * (V * (1 + L)) ^ m * (A₀ * Real.exp (-ε * rootLog a α.val)) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ₀ hσ _) (mul_nonneg hC (Real.sqrt_nonneg _)))
        (hGeom q hq hq₁) (pow_nonneg hq.le _)
        (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
          (pow_nonneg (mul_nonneg hV (by linarith)) _))
    _ = _ := by rw [mul_pow]; ring

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- A strict normalized exponent bound along a fundamental ray gives exponential
decay in that root logarithm, uniformly in the chamber and the compact right factors. -/
def AdelicSiegelRayDecayStatement : Prop :=
  StandardNestedHalfModulusCompatibilityStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ (J : StandardIndex F G fam.i fam.ν) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (f : AdelicGroupPoints F G → ℂ)
      (s : Finset (ComplexCharacterParameter F (fam.P J)))
      (c : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ),
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho J f s c →
    fam.HasSiegelChamberGrowth j rho f →
    let Δ := simpleRelativeRoots fam.i fam.ν
    let chamber := weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν
    let L := fun (a : intrinsicSubgroup F T₀) (β : characterLattice fam.T) =>
      characterLog F T₀.toGrp a.val (j ≫ β)
    ∀ (α : Δ) (r : intrinsicSubgroup F T₀), (∀ n : ℕ, r ^ n ∈ chamber 1) →
    0 < L r α.val → (∀ β ∈ Δ, β ≠ α.val → L r β = 0) →
    ∀ (b : fam.positiveSplitComponent J),
      map F (fam.P J) G (fam.p J) b.val = positiveMap F G fam.T fam.i T₀ j r →
    (∀ lam ∈ s, c lam ≠ 0 → ‖parameterPower F (fam.P J) lam b.val‖ < 1) →
    ∀ (t : ℝ≥0ˣ) (Ω : Set (AdelicGroupPoints F G)), IsCompact Ω →
      ∃ ε : ℝ, 0 < ε ∧ ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
        ∀ a ∈ chamber t, ∀ w ∈ Ω, ∀ R : ℝ, 0 ≤ R →
          (∀ β ∈ Δ, L a β ≤ R) →
          ‖f (positiveMap F G fam.T fam.i T₀ j a * w)‖ ≤
            C * Real.sqrt (siegelModulus F G fam.T fam.i fam.ν T₀ j a) * (1 + R) ^ m *
              Real.exp (-ε * L a α.val)

theorem adelicSiegelRayDecay : AdelicSiegelRayDecayStatement := by
  intro hδ F _ _ G _ _ _ fam T₀ j hsetup N d rho hN J hsmooth Kinf f s c hDec hGrow Δ chamber L
    α r hr hPos hOff b hb hStrict t Ω hΩ
  exact fam.exists_siegelChamberRayDecay_of_exponentDecomposition j rho hδ hsetup hN J hDec hGrow
    α r hr hPos hOff b hb hStrict t Ω hΩ

end Langlands.Global
