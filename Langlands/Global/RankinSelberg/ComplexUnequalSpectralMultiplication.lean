import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Langlands.Global.RankinSelberg.OrdinaryPolynomialGeneration
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness
import Langlands.Global.RankinSelberg.ArchimedeanComplexPairFactor
import Langlands.Representation.GodementJacquet.ComplexJacquetDeterminantWeight
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Spectral multiplication for ordinary complex unequal-rank integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalSpectralMultiplication

open Langlands.Archimedean (matrixModel rightDerivative rightDerivative_eq_fderiv
  unitsExtension unitsExtension_val differentiableAt_unitsExtension)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits_val)
open Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration (rightTranslate_mk)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexUnequalFamily (HasLeftCharacter HalfPlaneDomination ordinaryKernel_mk
  ordinary_halfPlaneDomination continuous_ordinaryKernel)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open Polynomial

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear (n + 1) ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "ρ" => ArchimedeanLocal.translateFunction

private def firstDirection (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

private def firstDilation (n : ℕ) (x : ℝ) : G n :=
  GeneralLinear.Iwasawa.diagonalUnits (fun i => if i = 0 then
    Units.mk0 (Complex.exp (x : ℂ)) (Complex.exp_ne_zero _) else 1)

private theorem firstDilation_val_eq_exp (n : ℕ) (x : ℝ) :
    (firstDilation n x).val = NormedSpace.exp (x • firstDirection n) := by
  rw [firstDilation, diagonalUnits_val, firstDirection, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  by_cases hi : i = 0 <;> simp [hi, Complex.real_smul]

private theorem firstDilation_zero (n : ℕ) : firstDilation n 0 = 1 := by
  apply Units.ext
  rw [firstDilation_val_eq_exp, zero_smul, NormedSpace.exp_zero, Units.val_one]

private theorem continuous_firstDilation (n : ℕ) : Continuous (firstDilation n) := by
  apply (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (n + 1)).isInducing.continuous_iff.mpr
  simp only [Function.comp_def, firstDilation_val_eq_exp]
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

private theorem padGL_firstDilation {r t : ℕ} (h : t < r) (x : ℝ) :
    padGL (Nat.succ_le_succ h.le) (firstDilation t x) = firstDilation r x := by
  apply Units.ext
  ext i j
  rw [UnequalAnalytic.padGL_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : (i : ℕ) < t + 1
    · rw [dite_eq_left ⟨hi, hi⟩]
      simp only [firstDilation, diagonalUnits_val, Matrix.diagonal_apply_eq]
      have hzero : (⟨i.val, hi⟩ : Fin (t + 1)) = 0 ↔ i = 0 := by
        constructor
        · intro he
          exact Fin.ext (congrArg (fun v : Fin (t + 1) => v.val) he)
        · intro he
          exact Fin.ext (congrArg (fun v : Fin (r + 1) => v.val) he)
      simp only [hzero]
    · rw [dite_eq_right (fun hh => hi hh.1)]
      have hiz : i ≠ 0 := fun hz => hi (by simp [hz])
      simp [firstDilation, diagonalUnits_val, hiz]
  · by_cases hsmall : (i : ℕ) < t + 1 ∧ (j : ℕ) < t + 1
    · rw [dite_eq_left hsmall]
      have hh : (⟨i.val, hsmall.1⟩ : Fin (t + 1)) ≠ ⟨j.val, hsmall.2⟩ := fun he =>
        hij (Fin.ext (congrArg (fun v : Fin (t + 1) => v.val) he))
      simp [firstDilation, diagonalUnits_val, Matrix.diagonal_apply_ne _ hh, Matrix.diagonal_apply_ne _ hij]
    · rw [dite_eq_right hsmall]
      simp [firstDilation, diagonalUnits_val, Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]

private theorem detPower_firstDilation (n : ℕ) (x : ℝ) (s : ℂ) :
    P (firstDilation n x) s = Complex.exp (2 * (x : ℂ) * s) := by
  have hdet : (firstDilation n x).val.det = Complex.exp (x : ℂ) := by
    rw [firstDilation, diagonalUnits_val, Matrix.det_diagonal, Finset.prod_eq_single (0 : Fin (n + 1))]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [ArchimedeanLocal.detPower, hdet, complexNormalizedAbs, Complex.norm_exp,
    Complex.ofReal_re, pow_two, ← Real.exp_add, Real.log_exp, Complex.ofReal_add]
  congr 1
  ring

private theorem hasDerivAt_firstDilation_translate {n : ℕ} {W : G n → ℂ}
    (hW : ContMDiff (matrixModel ℂ (n + 1)) 𝓘(ℝ, ℂ) ∞ W) (y : G n) (x : ℝ) :
    HasDerivAt (fun u : ℝ => W (y * firstDilation n u))
      (rightDerivative (matrixModel ℂ (n + 1)) (firstDirection n) W (y * firstDilation n x)) x := by
  let g := y * firstDilation n x
  have hu (u : ℝ) : (y * firstDilation n u).val = y.val * NormedSpace.exp (u • firstDirection n) := by
    rw [Units.val_mul, firstDilation_val_eq_exp]
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (firstDirection n) x).const_mul y.val
  have hγ : HasDerivAt (fun u : ℝ => (y * firstDilation n u).val)
      (g.val * firstDirection n) x := by
    simpa only [hu, g, mul_assoc] using h
  have hc := (differentiableAt_unitsExtension hW g.isUnit).hasFDerivAt.comp_hasDerivAt x hγ
  have hcomp : (unitsExtension W ∘ fun u : ℝ => (y * firstDilation n u).val) =
      fun u : ℝ => W (y * firstDilation n u) := funext fun _ => unitsExtension_val _ _
  rw [hcomp] at hc
  rw [rightDerivative_eq_fderiv hW]
  exact hc

variable {r t : ℕ} (h : t < r) {d e : List ComplexCharacterData} (a : ℂˣ)
variable (D : ComplexQuotientMeasureData t)

private theorem leftCharacter_translate {n : ℕ} {ds : List ComplexCharacterData} {b : ℂˣ}
    (W : complexWhittakerModel n ds b) (g : G n) : HasLeftCharacter b (ρ g W.val) := by
  intro u y
  change W.val ((u.val * y) * g) = _
  rw [mul_assoc]
  exact complexWhittakerModel_left_equivariant W.2 u.val u.2 (y * g)

private theorem unequalIntegral_firstDilation
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel t e (-a)) (x : ℝ) (s : ℂ) :
    complexUnequalIntegral h D (ρ (firstDilation r x) W.val) (ρ (firstDilation t x) V.val) s =
      Complex.exp ((x : ℂ) * (-2 * (s - ((r - t : ℕ) : ℂ) / 2))) * complexUnequalIntegral h D W.val V.val s := by
  let u := firstDilation t x
  let z := s - ((r - t : ℕ) : ℂ) / 2
  let m := Complex.exp ((x : ℂ) * (-2 * z))
  let E := Langlands.QuotientIntegration.rightTranslate (GeneralLinear.upperUnipotent (t + 1) ℂ) u
  have hm : MeasurePreserving E D.measure D.measure := by
    let := D.unipotentHaar_rightInvariant
    exact D.compatible.right_invariant u
  have hLeftW : HasLeftCharacter a W.val := fun n g => complexWhittakerModel_left_equivariant W.2 n.val n.2 g
  have hLeftV : HasLeftCharacter (-a) V.val := fun n g => complexWhittakerModel_left_equivariant V.2 n.val n.2 g
  have hK : complexUnequalIntegrand h (ρ (firstDilation r x) W.val) (ρ u V.val) s =
      fun q => m * complexUnequalIntegrand h W.val V.val s (E q) := by
    funext q
    induction q using Quotient.inductionOn with
    | _ g =>
      rw [show E (Quotient.mk _ g) = Quotient.mk _ (g * u) from rightTranslate_mk _ _ _,
        ordinaryKernel_mk h (leftCharacter_translate W _) (leftCharacter_translate V _),
        ordinaryKernel_mk h hLeftW hLeftV]
      have hu : padGL (Nat.succ_le_succ h.le) (g * u) =
          padGL (Nat.succ_le_succ h.le) g * firstDilation r x := by
        rw [map_mul, show u = firstDilation t x from rfl, padGL_firstDilation h]
      have hz : m * P u z = 1 := by
        rw [show u = firstDilation t x from rfl, detPower_firstDilation]
        dsimp only [m]
        rw [← Complex.exp_add, show (x : ℂ) * (-2 * z) + 2 * x * z = 0 by ring,
          Complex.exp_zero]
      dsimp only [ArchimedeanLocal.translateFunction]
      rw [hu, Langlands.GodementJacquet.detPower_complex_mul]
      calc
        _ = (m * P u z) * _ := by rw [hz, one_mul]
        _ = _ := by ring
  change (∫ q, complexUnequalIntegrand h (ρ (firstDilation r x) W.val) (ρ u V.val) s q ∂D.measure) = _
  rw [hK, integral_const_mul, hm.integral_comp E.measurableEmbedding]
  rfl


private def firstRightDerivative {n : ℕ} {ds : List ComplexCharacterData} {b : ℂˣ}
    (W : complexWhittakerModel n ds b) : complexWhittakerModel n ds b :=
  ⟨rightDerivative (matrixModel ℂ (n + 1)) (firstDirection n) W.val,
    rightDerivative_mem_complexWhittakerModel W.2 (firstDirection n)⟩

private def dilationKernel (W : G r → ℂ) (V : G t → ℂ) (s : ℂ) (x : ℝ) : Q t → ℂ :=
  complexUnequalIntegrand h (ρ (firstDilation r x) W) (ρ (firstDilation t x) V) s

private theorem dilationKernel_measurable
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel t e (-a)) (s : ℂ) (x : ℝ) :
    AEStronglyMeasurable (dilationKernel h W.val V.val s x) D.measure := by
  have hWc := (contMDiff_of_mem_complexWhittakerModel W.2).continuous
  have hVc := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  exact (continuous_ordinaryKernel h (leftCharacter_translate W _) (leftCharacter_translate V _)
    (hWc.comp (continuous_id.mul_const _)) (hVc.comp (continuous_id.mul_const _)) s).aestronglyMeasurable

private theorem dilationKernel_domination
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel t e (-a)) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → ∃ M : Q t → ℝ, Integrable M D.measure ∧
      ∀ x ∈ Icc (-1 : ℝ) 1, ∀ q : Q t, ‖dilationKernel h W.val V.val s x q‖ ≤ M q := by
  let S := Icc (-1 : ℝ) 1 ×ˢ (univ : Set ℂ)
  let W' (p : ℝ × ℂ) := ρ (firstDilation r p.1) W.val
  let V' (p : ℝ × ℂ) := ρ (firstDilation t p.1) V.val
  have hB {n : ℕ} {ds : List ComplexCharacterData} {b : ℂˣ} (U : complexWhittakerModel n ds b) :
      HasUniformSimpleRootBound S (fun p => ρ (firstDilation n p.1) U.val) := by
    let C := (firstDilation n) '' Icc (-1 : ℝ) 1
    obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound U C
      (isCompact_Icc.image (continuous_firstDilation n))
    refine ⟨N, fun J => ?_⟩
    obtain ⟨M, hM, hUb⟩ := hN J
    exact ⟨M, hM, fun p hp g => hUb (firstDilation n p.1) ⟨p.1, hp.1, rfl⟩ g⟩
  obtain ⟨b, hb⟩ := ordinary_halfPlaneDomination h D S W' V' Prod.snd
    (fun p => leftCharacter_translate W _) (fun p => leftCharacter_translate V _) (hB W) (hB V)
  refine ⟨b, fun s hs => ?_⟩
  obtain ⟨M, hM, hbd⟩ := hb s.re
  exact ⟨M, hM, fun x hx q => hbd (x, s) ⟨hx, mem_univ _⟩ hs le_rfl q⟩

private theorem hasDerivAt_dilationKernel
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel t e (-a))
    (s : ℂ) (q : Q t) (x : ℝ) :
    HasDerivAt (fun y : ℝ => dilationKernel h W.val V.val s y q)
      (dilationKernel h (firstRightDerivative W).val V.val s x q +
        dilationKernel h W.val (firstRightDerivative V).val s x q) x := by
  have hW := hasDerivAt_firstDilation_translate (contMDiff_of_mem_complexWhittakerModel W.2)
    (padGL (Nat.succ_le_succ h.le) q.out) x
  have hV := hasDerivAt_firstDilation_translate (contMDiff_of_mem_complexWhittakerModel V.2) q.out x
  have hD := (hW.mul hV).mul_const (P q.out (s - ((r - t : ℕ) : ℂ) / 2))
  simpa only [dilationKernel, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    ArchimedeanLocal.translateFunction, firstRightDerivative, Pi.mul_apply, add_mul, add_comm] using hD

/-- In the ordinary unequal-rank convergence half-plane, the first diagonal right Lie
derivatives of the two coefficients realize multiplication by the shifted spectral parameter. -/
private theorem exists_unequalIntegral_spectralDerivative
    (W : complexWhittakerModel r d a) (V : complexWhittakerModel t e (-a)) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      complexUnequalIntegral h D (firstRightDerivative W).val V.val s +
        complexUnequalIntegral h D W.val (firstRightDerivative V).val s =
      (-2 * (s - ((r - t : ℕ) : ℂ) / 2)) * complexUnequalIntegral h D W.val V.val s := by
  let W₁ := firstRightDerivative W
  let V₁ := firstRightDerivative V
  obtain ⟨b, hb⟩ := dilationKernel_domination h a D W V
  obtain ⟨b₁, hb₁⟩ := dilationKernel_domination h a D W₁ V
  obtain ⟨b₂, hb₂⟩ := dilationKernel_domination h a D W V₁
  refine ⟨max b (max b₁ b₂), fun s hs => ?_⟩
  obtain ⟨M, hM, hMB⟩ := hb s ((le_max_left _ _).trans_lt hs)
  obtain ⟨M₁, hM₁, hMB₁⟩ := hb₁ s ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  obtain ⟨M₂, hM₂, hMB₂⟩ := hb₂ s ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs))
  let F := dilationKernel h W.val V.val s
  let A := dilationKernel h W₁.val V.val s
  let B := dilationKernel h W.val V₁.val s
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hF := dilationKernel_measurable h a D W V s
  have hA := dilationKernel_measurable h a D W₁ V s
  have hB := dilationKernel_measurable h a D W V₁ s
  have hi : Integrable (F 0) D.measure := hM.mono' (hF 0) (ae_of_all _ (hMB 0 h0))
  have hi₁ : Integrable (A 0) D.measure := hM₁.mono' (hA 0) (ae_of_all _ (hMB₁ 0 h0))
  have hi₂ : Integrable (B 0) D.measure := hM₂.mono' (hB 0) (ae_of_all _ (hMB₂ 0 h0))
  have hnb : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F)
    (F' := fun x q => A x q + B x q) hnb (Eventually.of_forall hF) hi ((hA 0).add (hB 0))
    (ae_of_all _ fun q x hx => (norm_add_le _ _).trans (add_le_add (hMB₁ x hx q) (hMB₂ x hx q)))
    (hM₁.add hM₂) (ae_of_all _ fun q x _ => hasDerivAt_dilationKernel h a W V s q x)
  let z := -2 * (s - ((r - t : ℕ) : ℂ) / 2)
  have hEq : (fun x : ℝ => ∫ q, F x q ∂D.measure) =
      fun x : ℝ => Complex.exp ((x : ℂ) * z) * complexUnequalIntegral h D W.val V.val s :=
    funext fun x => unequalIntegral_firstDilation h a D W V x s
  have hD' : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * z) * complexUnequalIntegral h D W.val V.val s)
      (z * complexUnequalIntegral h D W.val V.val s) 0 := by
    simpa only [id_eq, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.ofReal_one, one_mul] using
      ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const z).cexp).mul_const
        (complexUnequalIntegral h D W.val V.val s)
  rw [hEq] at hderiv
  have hVal := hderiv.unique hD'
  dsimp only at hVal
  rw [integral_add hi₁ hi₂] at hVal
  have hone {n : ℕ} (U : G n → ℂ) : ρ (1 : G n) U = U := by
    funext y
    simp [ArchimedeanLocal.translateFunction]
  simpa only [A, B, dilationKernel, firstDilation_zero, hone, W₁, V₁, z,
    complexUnequalIntegral, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegral] using hVal

/-- If each complex unequal test admits a polynomial normalization and its normalized
values cover every point, then finitely many normalized values sum to one. -/
def ComplexUnequalFiniteSumFromPolynomialsStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (d e : List ComplexCharacterData) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t),
    let I := complexOrdinaryUnequalTest h d e a D
    let L := complexPairLFactor d e
    (∀ i, ∃ (p : ℂ[X]) (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹)),
      ∀ s, N.value s = p.eval s) →
    HasCoveringOrdinaryNormalizations I L →
    HasFiniteOrdinaryNormalizationSum I L

set_option maxHeartbeats 900000 in
theorem complexUnequalFiniteSumFromPolynomials : ComplexUnequalFiniteSumFromPolynomialsStatement := by
  intro r t h d e a D I L hPoly hCover
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0 :=
    ArchimedeanComplexPairFactor.complexLFactor_ne_zero _
  refine ordinaryPolynomialGeneration I L ?_ (fun c p hp =>
    isOrdinaryNormalizationPolynomial_complexUnequal_smul h d e a D c hp) ?_
  · intro s
    obtain ⟨i, N, hN⟩ := hCover s
    obtain ⟨p, M, hM⟩ := hPoly i
    have he := N.value_eq_of_factor_ne_zero M ⟨b, fun z hz => inv_ne_zero (hb z hz)⟩
    rw [he, hM] at hN
    exact ⟨p, ⟨i, M, hM⟩, hN⟩
  · intro p hp
    obtain ⟨⟨W, V⟩, N, hN⟩ := hp
    obtain ⟨p₁, N₁, hN₁⟩ := hPoly (firstRightDerivative W, V)
    obtain ⟨p₂, N₂, hN₂⟩ := hPoly (W, firstRightDerivative V)
    obtain ⟨b₀, hb₀⟩ := exists_unequalIntegral_spectralDerivative h a D W V
    obtain ⟨bI, hI⟩ := N.eq_on_right
    obtain ⟨b₁, h₁⟩ := N₁.eq_on_right
    obtain ⟨b₂, h₂⟩ := N₂.eq_on_right
    let B := max b (max b₀ (max bI (max b₁ b₂)))
    let γ : ℂ := ((r - t : ℕ) : ℂ) / 2
    let q : ℂ[X] := γ • p - (1 / 2 : ℂ) • (p₁ + p₂)
    have hpq : X * p = q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hInf : (Complex.ofReal '' Ioi B).Infinite :=
        (Set.Ioi_infinite B).image Complex.ofReal_injective.injOn
      apply hInf.mono
      rintro z ⟨x, hx, rfl⟩
      let s : ℂ := x
      have hs : B < s.re := by simpa only [s, Complex.ofReal_re, mem_Ioi] using hx
      have hmax := (le_max_right b _).trans_lt hs
      have hmax' := (le_max_right b₀ _).trans_lt hmax
      have hmax'' := (le_max_right bI _).trans_lt hmax'
      have h₀ := hI s ((le_max_left bI _).trans_lt hmax')
      have h₁' := h₁ s ((le_max_left b₁ b₂).trans_lt hmax'')
      have h₂' := h₂ s ((le_max_right b₁ b₂).trans_lt hmax'')
      have hderiv := hb₀ s ((le_max_left b₀ _).trans_lt hmax)
      change I (firstRightDerivative W, V) s + I (W, firstRightDerivative V) s =
        (-2 * (s - γ)) * I (W, V) s at hderiv
      rw [h₁', h₂', h₀, hN₁, hN₂, hN, ← add_mul, ← mul_assoc] at hderiv
      have he := mul_right_cancel₀ (inv_ne_zero (hb s ((le_max_left b _).trans_lt hs))) hderiv
      change (X * p).eval s = q.eval s
      simp only [q, eval_sub, smul_eq_C_mul, eval_mul, eval_C, eval_add, eval_X]
      linear_combination (1 / 2 : ℂ) * he
    rw [hpq]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, N, hN⟩))
      (Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, N₁, hN₁⟩)
        (Submodule.subset_span ⟨_, N₂, hN₂⟩)))

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalSpectralMultiplication
