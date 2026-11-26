import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.ArchimedeanRealPairFactor
import Langlands.Global.RankinSelberg.RealAdjacentGodementHalfPlane
import Langlands.Global.RankinSelberg.RealGodementGaussianSpanning
import Langlands.Global.RankinSelberg.RealGodementSchwartzJoint
import Langlands.Global.RankinSelberg.RealGodementCanonicalModel
import Langlands.Global.RankinSelberg.RealGodementLeadingFamily
import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests

/-! # A normalized real `GL₂ × GL₁` test in the closed character chamber -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal NNReal SchwartzMap Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000

namespace Langlands.Global.RankinSelbergGlobal.RealAdjacentRankOne

open ArchimedeanLocal RealJacquet RealGodement RealRankZero RealGodementProfiles
open Langlands.Archimedean Langlands.Archimedean.GramFormula
open Langlands.Archimedean.PartialJacquet Langlands.LocalFactor.Archimedean
open Langlands.LocalFactor.RealTate
open RealJacquetFrobenius (charData)
open RealRankOneStandardModule (characterVector characterVector_mul characterVector_mem)
open RealGodementGaussianPolynomial
open Langlands.GodementJacquet (tateScalarEquiv)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

private local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
private local instance : MeasurableSpace ℝˣ := borel _
private local instance : BorelSpace ℝˣ := ⟨rfl⟩

local notation "H" => Langlands.GeneralLinear 1 ℝ
local notation "G" => Langlands.GeneralLinear 2 ℝ
local notation "M" => Matrix (Fin 1) (Fin 1) ℝ
local notation "Row" => Fin 1 → ℝ
local notation "X" => Matrix (Fin 1) (Fin 2) ℝ

private def rankOneMatrixCoordinate : M ≃L[ℝ] ℝ := by
  let L : M →ₗ[ℝ] ℝ := Matrix.entryLinearMap ℝ ℝ (0 : Fin 1) (0 : Fin 1)
  refine (LinearEquiv.ofBijective L ⟨?_, fun x => ⟨fun _ _ => x, rfl⟩⟩).toContinuousLinearEquiv
  intro A B h
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  exact h

private def matrixTateGaussian (p : Fin 2) : 𝓢(M, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rankOneMatrixCoordinate (gaussSchwartzE p)

private theorem matrixTateGaussian_apply (p : Fin 2) (A : M) :
    matrixTateGaussian p A = gaussian p (A 0 0) := gaussSchwartzE_apply p _

private def rowTateGaussian (p : Fin 2) : 𝓢(Row, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
    (gaussSchwartzE p)

private theorem rowTateGaussian_apply (p : Fin 2) (x : Row) :
    rowTateGaussian p x = gaussian p (x 0) := gaussSchwartzE_apply p _

private theorem lineSchwartz_rowTateGaussian (p : Fin 2) :
    lineSchwartz (rowTateGaussian p) = gaussSchwartzE p := by
  ext x
  rfl

private theorem realRowSchwartzFourier_one (p : Fin 2) :
    realRowSchwartzFourier 1 1 (rowTateGaussian p) = I ^ p.val • rowTateGaussian p := by
  ext x
  have hx : (fun _ : Fin 1 => x 0) = x := funext fun j => congrArg x (Subsingleton.elim _ _)
  nth_rw 1 [← hx]
  rw [realRowSchwartzFourier_apply, realFourierTransform_const, lineSchwartz_rowTateGaussian]
  have h : NNReal.sqrt ‖((1 : ℝˣ) : ℝ)‖₊ = 1 := by simp
  rw [h, tateFourier, smul_apply, smul_eq_mul, rowTateGaussian_apply]
  simpa only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, one_mul, gaussSchwartzE_apply]
    using integral_exp_mul_gaussian p (x 0)

private theorem exists_groupHaar_eq (D : RealQuotientMeasureData 0) :
    ∃ k : ℝ≥0, k ≠ 0 ∧ D.groupHaar = k • unitsHaar.map (tateScalarEquiv ℝ) := by
  let μ := unitsHaar.map (tateScalarEquiv ℝ)
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : μ.IsHaarMeasure := (tateScalarEquiv ℝ).isHaarMeasure_map unitsHaar
  let : SecondCountableTopology H :=
    Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  have he := Measure.isMulLeftInvariant_eq_smul D.groupHaar μ
  refine ⟨Measure.haarScalarFactor D.groupHaar μ, ?_, he⟩
  intro h
  have hpos := isOpen_univ.measure_pos (μ := D.groupHaar)
    (Set.univ_nonempty : (Set.univ : Set H).Nonempty)
  rw [he, h, zero_smul, Measure.coe_zero, Pi.zero_apply] at hpos
  exact lt_irrefl _ hpos

private theorem matrixZeta_eq (D : RealQuotientMeasureData 0) (c e : RealCharacterData)
    {k : ℝ≥0} (hk : D.groupHaar = k • unitsHaar.map (tateScalarEquiv ℝ)) (s : ℂ) :
    (∫ z : H, matrixTateGaussian (c.mul e).parity z.val *
      (c.character (GeneralLinear.determinant z) : ℂ) * (e.character (GeneralLinear.determinant z) : ℂ) *
      ArchimedeanLocal.detPower realNormalizedAbs z s ∂D.groupHaar) =
    (k : ℂ) * zeta (gaussSchwartzE (c.mul e).parity) (c.mul e).parity (s + (c.mul e).exponent) := by
  have hEmb : MeasurableEmbedding (tateScalarEquiv ℝ : ℝˣ → H) :=
    (tateScalarEquiv ℝ).toHomeomorph.measurableEmbedding
  rw [hk, integral_smul_nnreal_measure, hEmb.integral_map]
  rw [NNReal.smul_def, Complex.real_smul]
  congr 1
  let Z (x : ℝ) : ℂ := gaussSchwartzE (c.mul e).parity x *
    (((x / |x| : ℝ) : ℂ) ^ (c.mul e).parity.val * ((|x| : ℝ) : ℂ) ^ (s + (c.mul e).exponent))
  have hZ (u : ℝˣ) : matrixTateGaussian (c.mul e).parity (tateScalarEquiv ℝ u).val *
      (c.character (GeneralLinear.determinant (tateScalarEquiv ℝ u)) : ℂ) *
      (e.character (GeneralLinear.determinant (tateScalarEquiv ℝ u)) : ℂ) *
      ArchimedeanLocal.detPower realNormalizedAbs (tateScalarEquiv ℝ u) s = Z u := by
    have hval : (tateScalarEquiv ℝ u).val 0 0 = (u : ℝ) := by
      rw [← RealRankZero.det_val_tateScalarEquiv u, Matrix.det_fin_one]
    rw [matrixTateGaussian_apply, hval, determinant_tateScalarEquiv, detPower_tateScalarEquiv]
    rw [mul_assoc (gaussian _ _) _ _, character_mul_character]
    simp only [Z, gaussSchwartzE_apply]
    rw [Complex.cpow_add s (c.mul e).exponent
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr u.ne_zero))]
    ring
  rw [show (∫ u : ℝˣ, _ ∂unitsHaar) = ∫ u : ℝˣ, Z u ∂unitsHaar from integral_congr_ae (ae_of_all _ hZ),
    integral_unitsHaar, zeta]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
  simp only [Z, integrand, ite_eq_right hx]
  have hpow : ((|x|⁻¹ : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s + (c.mul e).exponent) =
      ((|x| : ℝ) : ℂ) ^ (s + (c.mul e).exponent - 1) := by
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx))]
    congr 1
    ring
  linear_combination (gaussSchwartzE (c.mul e).parity x * ((x / |x| : ℝ) : ℂ) ^ (c.mul e).parity.val) * hpow

private theorem realAdjacentUnfoldedIntegral_gaussians (D : RealQuotientMeasureData 0)
    (c d e : RealCharacterData) {q k : ℝ≥0}
    (hq : D.measure = q • unitsHaar.map quotientUnits.symm)
    (hk : D.groupHaar = k • unitsHaar.map (tateScalarEquiv ℝ)) (s : ℂ)
    (hs₁ : 0 < (s + (c.mul e).exponent).re) (hs₂ : 0 < (s + (d.mul e).exponent).re) :
    realAdjacentUnfoldedIntegral D c.character.toMonoidHom (matrixTateGaussian (c.mul e).parity)
        (rowTateGaussian (d.mul e).parity) (characterVector d) (characterVector e) s =
      ((q : ℂ) * (k : ℂ)) * Gammaℝ (s + (c.mul e).exponent + (c.mul e).parity.val) *
        Gammaℝ (s + (d.mul e).exponent + (d.mul e).parity.val) := by
  let Φ := rowTateGaussian (d.mul e).parity
  let J := realEqualIntegral D (characterVector d) (characterVector e) Φ s
  have hShift (z : H) :
      realEqualIntegral D (characterVector d) (fun x => characterVector e (x * z)) Φ s =
        characterVector e z * J := by
    change (∫ x, realEqualIntegrand (characterVector d) (fun y => characterVector e (y * z)) Φ s x
      ∂D.measure) = characterVector e z *
        (∫ x, realEqualIntegrand (characterVector d) (characterVector e) Φ s x ∂D.measure)
    rw [← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand]
    rw [characterVector_mul]
    ring
  have hUnfolded : realAdjacentUnfoldedIntegral D c.character.toMonoidHom
      (matrixTateGaussian (c.mul e).parity) Φ (characterVector d) (characterVector e) s =
      J * (∫ z : H, matrixTateGaussian (c.mul e).parity z.val * (c.character (GeneralLinear.determinant z) : ℂ) *
        (e.character (GeneralLinear.determinant z) : ℂ) *
          ArchimedeanLocal.detPower realNormalizedAbs z s ∂D.groupHaar) := by
    unfold realAdjacentUnfoldedIntegral
    rw [← integral_const_mul]
    apply integral_congr_ae (ae_of_all _ fun z => ?_)
    rw [hShift]
    simp only [realAdjacentMatrixWeight, detCharacter, Nat.cast_zero, zero_div, add_zero]
    change characterVector e z * J * (_ * (c.character (GeneralLinear.determinant z) : ℂ) * _) =
      J * (_ * (c.character (GeneralLinear.determinant z) : ℂ) * characterVector e z * _)
    ring
  rw [hUnfolded, matrixZeta_eq D c e hk, zeta_gaussSchwartzE _ hs₁]
  have hJ : J = (q : ℂ) * Gammaℝ (s + (d.mul e).exponent + (d.mul e).parity.val) := by
    change realEqualIntegral D (characterVector d) (characterVector e) Φ s = _
    rw [equalIntegral_eq d e (W := characterVector d) (W' := characterVector e)
      (C := 1) (C' := 1) hq (fun _ => (one_mul _).symm) (fun _ => (one_mul _).symm),
      lineSchwartz_rowTateGaussian, zeta_gaussSchwartzE _ hs₂, one_mul, one_mul]
  rw [hJ]
  ring

private theorem rankOneCharacter_mem_uniform (d : RealCharacterData) (a : ℝˣ) :
    characterVector d ∈ realUniformWhittakerModel 0 [.character d] (-a) := by
  let f : Automorphic.realStandardKFinite 1 [.character d] := ⟨characterVector d, characterVector_mem d⟩
  have hd : IsStrictlyDominant (realPositionExponent [.character d]) 0 := fun _ h => (Nat.not_lt_zero _ h).elim
  have h := realGodementOpenCellModel 0 [.character d] a hd f
  simpa only [funext (additiveJacquetIntegral_rankOne a f.val)] using h

private theorem sectionValue_const_mul (μ : Measure H) (c : RealCharacterData) (f : H → ℂ)
    (l : ℂ) (Φ : X → ℂ) (g : G) :
    sectionValue μ c f (fun Y => l * Φ Y) g = l * sectionValue μ c f Φ g := by
  simp only [sectionValue_eq_integral]
  have h : (fun h : H => f h⁻¹ * determinantWeight c 1 h * (l * Φ (rowPoint h.val g))) =
      fun h => l * (f h⁻¹ * determinantWeight c 1 h * Φ (rowPoint h.val g)) := by
    funext h
    ring
  have hExp : (((1 : ℕ) : ℂ) + 1) / 2 = 1 := by norm_num
  simp only [hExp, h, integral_const_mul]
  ring

private theorem rightTranslate_scalar_mem_kFinite (χ : ℕ → ℝˣ → ℂ) (u : ℝˣ) {F : G → ℂ}
    (hF : F ∈ kFiniteFunctions (principalSeries ℝ 2 χ) (unitaryCompact ℝ 2)) :
    Whittaker.rightTranslation ℂ G (GeneralLinear.scalar u) F ∈
      kFiniteFunctions (principalSeries ℝ 2 χ) (unitaryCompact ℝ 2) := by
  let s : G := GeneralLinear.scalar u
  let L := Whittaker.rightTranslation ℂ G s
  refine ⟨rightTranslation_mem_principalSeries _ hF.1 s, ?_⟩
  have hfin := (mem_kFiniteVectors_iff _ _ _).mp hF.2
  let U := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 2 =>
    Whittaker.rightTranslation ℂ G k.val F)
  let : FiniteDimensional ℂ U := hfin
  apply (mem_kFiniteVectors_iff _ _ _).mpr
  refine Submodule.finiteDimensional_of_le (S₂ := U.map L) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  funext g
  change F (g * s * k.val) = F (g * k.val * s)
  rw [mul_assoc, mul_assoc,
    show s * k.val = k.val * s from Matrix.GeneralLinearGroup.scalar_commute u k.val]

private def gaussianMonomial (p q : Fin 2) : MvPolynomial (Coordinates 1 2) ℂ :=
  MvPolynomial.X (0, 0) ^ p.val * MvPolynomial.X (0, 1) ^ q.val

private theorem columnProduct_eq_dilation (p q : Fin 2) (Y : X) :
    realColumnProduct (matrixTateGaussian p) (realRowSchwartzFourier 1 1 (rowTateGaussian q)) Y =
      (I ^ q.val / (Real.sqrt Real.pi : ℂ) ^ (p.val + q.val)) *
        gaussianPolynomial (gaussianMonomial p q) (Real.sqrt Real.pi • Y) := by
  have hLead : leadingColumns (r := 0) Y 0 0 = Y 0 0 := rfl
  have hLast : lastColumn (r := 0) Y 0 = Y 0 1 := rfl
  rw [realColumnProduct_apply (r := 0), realRowSchwartzFourier_one, smul_apply, smul_eq_mul,
    matrixTateGaussian_apply, rowTateGaussian_apply, hLead, hLast]
  simp only [gaussian, gaussianPolynomial_apply,
    gaussianMonomial, map_mul, map_pow, MvPolynomial.eval_X, coordinates, Matrix.smul_apply,
    matrixGaussian, matrixSqNorm, Fin.sum_univ_one, Fin.sum_univ_two]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_add, Complex.ofReal_pow, mul_pow]
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  simp only [hsq]
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hExp : Complex.exp (-(Real.pi : ℂ) * (Y 0 0 : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (Y 0 1 : ℂ) ^ 2) =
    Complex.exp (-(Real.pi * ((Y 0 0 : ℂ) ^ 2 + (Y 0 1 : ℂ) ^ 2))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = I ^ q.val * (Y 0 0 : ℂ) ^ p.val * (Y 0 1 : ℂ) ^ q.val *
        (Complex.exp (-(Real.pi : ℂ) * (Y 0 0 : ℂ) ^ 2) *
          Complex.exp (-(Real.pi : ℂ) * (Y 0 1 : ℂ) ^ 2)) := by ring
    _ = _ := by
      rw [hExp, pow_add]
      field_simp [hs]

private def columnGaussian (p q : Fin 2) : 𝓢(X, ℂ) :=
  realColumnProduct (matrixTateGaussian p) (realRowSchwartzFourier 1 1 (rowTateGaussian q))

private theorem gaussianColumnSection_mem (D : RealQuotientMeasureData 0)
    (c d : RealCharacterData) (hc : d.exponent.re ≤ c.exponent.re)
    (p q : Fin 2) :
    sectionValue D.groupHaar c (characterVector d) (columnGaussian p q) ∈
      Automorphic.realStandardKFinite 2 [.character c, .character d] := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let ds : List RealBlock := [.character d]
  let b : ℝˣ := Units.mk0 (Real.sqrt Real.pi) (Real.sqrt_pos.2 Real.pi_pos).ne'
  let z : G := GeneralLinear.scalar b
  let m : ℂ := I ^ q.val / (Real.sqrt Real.pi : ℂ) ^ (p.val + q.val)
  let Φ := gaussianPolynomial (gaussianMonomial p q)
  let Φπ := columnGaussian p q
  have hf : characterVector d ∈ principalSeries ℝ 1 (realPositionCharacter ds) :=
    (Submodule.mem_inf.mp (characterVector_mem d)).1.1
  have hStrip (j : Fin 1) : (1 : ℝ) + normExponent (realPositionExponent ds) 1 j ≤
      c.exponent.re + ((1 : ℝ) + 1) / 2 := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [normExponent, ds, realPositionExponent, add_comm] using hc
  have hF := gaussianSection_mem_kFinite D.groupHaar c ds hf
    (fun j => by simpa only [Nat.zero_add, Nat.cast_one] using hStrip j) (gaussianMonomial p q)
  have hFπ : sectionValue D.groupHaar c (characterVector d) Φπ =
      (m / determinantWeight c (1 / 2) z) • Whittaker.rightTranslation ℂ G z
        (sectionValue D.groupHaar c (characterVector d) Φ) := by
    have hDil (Y : X) : Y * z.val = Real.sqrt Real.pi • Y := by
      change Y * Matrix.diagonal (fun _ : Fin 2 => Real.sqrt Real.pi) = _
      ext i j
      rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    funext g
    change sectionValue D.groupHaar c (characterVector d) Φπ g =
      (m / determinantWeight c (1 / 2) z) * sectionValue D.groupHaar c (characterVector d) Φ (g * z)
    have hp : (Φπ : X → ℂ) = fun Y => m * Φ (Y * z.val) :=
      funext fun Y => by rw [hDil]; exact columnProduct_eq_dilation p q Y
    rw [hp, sectionValue_const_mul, sectionValue_mul_right]
    have hz := ((Group.isUnit z).map (determinantWeight c (1 / 2))).ne_zero
    rw [show (((0 + 1 : ℕ) : ℂ)) = 1 by norm_num]
    change m * _ = (m / determinantWeight c (1 / 2) z) * (determinantWeight c (1 / 2) z * _)
    field_simp [hz]
  have hStd : sectionValue D.groupHaar c (characterVector d) Φπ ∈
      kFiniteFunctions (principalSeries ℝ 2 (realPositionCharacter (.character c :: ds)))
        (unitaryCompact ℝ 2) := by
    rw [hFπ]
    exact Submodule.smul_mem _ _ (rightTranslate_scalar_mem_kFinite _ b hF)
  exact ⟨⟨hStd.1, fun p' u hp' => by
    cases p' with
    | zero => simp [realInducedBlockAt] at hp'
    | succ p' => cases p' <;> simp [realInducedBlockAt] at hp'⟩, hStd.2⟩

private def gaussianPower (n : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ n) (gaussSchwartzE 0)

private theorem gaussianPower_apply (n : ℕ) (x : ℝ) :
    gaussianPower n x = (x : ℂ) ^ n * gaussian 0 x := by
  have h : (fun y : ℝ => (y : ℂ) ^ n).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.pow n
  rw [gaussianPower, SchwartzMap.smulLeftCLM_apply_apply h,
    smul_eq_mul, gaussSchwartzE_apply]

private def angularValue (p q : Fin 2) (k : G) : ℂ :=
  I ^ q.val * (k.val 1 0 : ℂ) ^ p.val * (k.val 1 1 : ℂ) ^ q.val

private theorem columnGaussian_rowPoint (p q : Fin 2) (h : H) {k : G}
    (hk : k ∈ unitaryCompact ℝ 2) :
    columnGaussian p q (rowPoint h.val k) =
      angularValue p q k * gaussianPower (p.val + q.val) h.val.det := by
  have hRow (j : Fin 2) : rowPoint h.val k 0 j = h.val.det * k.val 1 j := by
    simp [rowPoint, Matrix.mul_apply, lastRows]
  have hNorm : k.val 1 0 ^ 2 + k.val 1 1 ^ 2 = 1 := by
    have hGram := congrArg (fun (A : Matrix (Fin 2) (Fin 2) ℝ) => A 1 1)
      (GramFormula.mul_transpose_eq_one_of_mem hk)
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, sq] using hGram
  let Y := rowPoint h.val k
  change columnGaussian p q Y = _
  have hLead : leadingColumns (r := 0) Y 0 0 = Y 0 0 := rfl
  have hLast : lastColumn (r := 0) Y 0 = Y 0 1 := rfl
  rw [columnGaussian, realColumnProduct_apply (r := 0), realRowSchwartzFourier_one, smul_apply,
    smul_eq_mul, matrixTateGaussian_apply, rowTateGaussian_apply, hLead, hLast,
    show Y 0 0 = h.val.det * k.val 1 0 from hRow 0,
    show Y 0 1 = h.val.det * k.val 1 1 from hRow 1, gaussianPower_apply]
  simp only [gaussian, Fin.val_zero, pow_zero, one_mul, Complex.ofReal_mul, mul_pow, angularValue]
  have hNormC : (k.val 1 0 : ℂ) ^ 2 + (k.val 1 1 : ℂ) ^ 2 = 1 := by exact_mod_cast hNorm
  have hExp : exp (-(Real.pi : ℂ) * ((h.val.det : ℂ) * (k.val 1 0 : ℂ)) ^ 2) *
      exp (-(Real.pi : ℂ) * ((h.val.det : ℂ) * (k.val 1 1 : ℂ)) ^ 2) =
        exp (-(Real.pi : ℂ) * (h.val.det : ℂ) ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    calc
      _ = (-(Real.pi : ℂ) * (h.val.det : ℂ) ^ 2) *
          ((k.val 1 0 : ℂ) ^ 2 + (k.val 1 1 : ℂ) ^ 2) := by ring
      _ = _ := by rw [hNormC, mul_one]
  rw [pow_add]
  calc
    _ = (I ^ q.val * (k.val 1 0 : ℂ) ^ p.val * (k.val 1 1 : ℂ) ^ q.val) *
        (((h.val.det : ℂ) ^ p.val * (h.val.det : ℂ) ^ q.val) *
          (exp (-(Real.pi : ℂ) * ((h.val.det : ℂ) * (k.val 1 0 : ℂ)) ^ 2) *
            exp (-(Real.pi : ℂ) * ((h.val.det : ℂ) * (k.val 1 1 : ℂ)) ^ 2))) := by ring_nf
    _ = _ := by rw [hExp]

private def radialMoment (D : RealQuotientMeasureData 0) (c d : RealCharacterData) (n : ℕ) : ℂ :=
  ∫ h : H, characterVector d h⁻¹ * determinantWeight c 1 h * gaussianPower n h.val.det ∂D.groupHaar

private theorem radialMoment_eq (D : RealQuotientMeasureData 0) (c d : RealCharacterData) (n : ℕ)
    {k : ℝ≥0} (hk : D.groupHaar = k • unitsHaar.map (tateScalarEquiv ℝ)) :
    radialMoment D c d n =
      (k : ℂ) * zeta (gaussianPower n) (c.mul d.inverse).parity (c.exponent - d.exponent + 1) := by
  have hEmb : MeasurableEmbedding (tateScalarEquiv ℝ : ℝˣ → H) :=
    (tateScalarEquiv ℝ).toHomeomorph.measurableEmbedding
  rw [radialMoment, hk, integral_smul_nnreal_measure, hEmb.integral_map, NNReal.smul_def, Complex.real_smul]
  congr 1
  let w := c.exponent - d.exponent + 1
  let E := (c.mul d.inverse).parity
  let Z (x : ℝ) : ℂ := gaussianPower n x *
    (((x / |x| : ℝ) : ℂ) ^ E.val * ((|x| : ℝ) : ℂ) ^ w)
  have hZ (u : ℝˣ) :
      characterVector d (tateScalarEquiv ℝ u)⁻¹ *
        determinantWeight c 1 (tateScalarEquiv ℝ u) *
          gaussianPower n (tateScalarEquiv ℝ u).val.det = Z u := by
    change (d.character (GeneralLinear.determinant (tateScalarEquiv ℝ u)⁻¹) : ℂ) *
      ((c.character (GeneralLinear.determinant (tateScalarEquiv ℝ u)) : ℂ) *
        ((|(GeneralLinear.determinant (tateScalarEquiv ℝ u) : ℝ)| : ℝ) : ℂ) ^ (1 : ℂ)) * _ = _
    rw [map_inv, determinant_tateScalarEquiv, det_val_tateScalarEquiv]
    have hmul : (d.character u⁻¹ : ℂ) * (c.character u : ℂ) = ((c.mul d.inverse).character u : ℂ) := by
      have hD : (d.character u⁻¹ : ℂ) = (d.inverse.character u : ℂ) := by
        change (d.character u⁻¹ : ℂ) = (((d.character u)⁻¹ : ℂˣ) : ℂ)
        rw [map_inv]
      rw [hD, mul_comm]
      rfl
    rw [← mul_assoc, hmul, (c.mul d.inverse).character_eq u]
    change _ = gaussianPower n (u : ℝ) * (((((u : ℝ) / |(u : ℝ)| : ℝ) : ℂ)) ^ E.val *
      ((|(u : ℝ)| : ℝ) : ℂ) ^ w)
    rw [show w = (c.mul d.inverse).exponent + 1 by simp [w, RealCharacterData.mul, RealCharacterData.inverse, sub_eq_add_neg],
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr u.ne_zero))]
    ring
  rw [show (∫ u : ℝˣ, _ ∂unitsHaar) = ∫ u : ℝˣ, Z u ∂unitsHaar from integral_congr_ae (ae_of_all _ hZ),
    integral_unitsHaar, zeta]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
  simp only [Z, integrand, ite_eq_right hx]
  have hpow : ((|x|⁻¹ : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ w = ((|x| : ℝ) : ℂ) ^ (w - 1) := by
    rw [Complex.ofReal_inv, ← Complex.cpow_neg_one,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx))]
    congr 1
    ring
  linear_combination (gaussianPower n x * ((x / |x| : ℝ) : ℂ) ^ E.val) * hpow

private theorem continuousAt_radialMoment (D : RealQuotientMeasureData 0) (p : Fin 2)
    (d : RealCharacterData) (n : ℕ) {z : ℂ} (hz : d.exponent.re ≤ z.re) :
    ContinuousAt (fun w => radialMoment D (charData p w) d n) z := by
  obtain ⟨k, _, hk⟩ := exists_groupHaar_eq D
  simp_rw [radialMoment_eq D _ d n hk]
  have hpos : 0 < (z - d.exponent + 1).re := by
    simp only [add_re, sub_re, one_re]
    linarith
  have hArg : ContinuousAt (fun w : ℂ => w - d.exponent + 1) z :=
    continuousAt_id.sub continuousAt_const |>.add continuousAt_const
  have hzeta := differentiableAt_zeta (gaussianPower n) (p + d.parity) hpos
  have hZ : ContinuousAt (fun w : ℂ => zeta (gaussianPower n) (p + d.parity) (w - d.exponent + 1)) z :=
    hzeta.continuousAt.comp' (f := fun w : ℂ => w - d.exponent + 1) hArg
  exact hZ.const_mul _

private theorem gaussianColumnSection_angular (D : RealQuotientMeasureData 0)
    (c d : RealCharacterData) (p q : Fin 2) {k : G} (hk : k ∈ unitaryCompact ℝ 2) :
    sectionValue D.groupHaar c (characterVector d) (columnGaussian p q) k =
      radialMoment D c d (p.val + q.val) * (determinantWeight c (1 / 2) k * angularValue p q k) := by
  change determinantWeight c (((1 : ℕ) : ℂ) / 2) k *
      (∫ h : H, characterVector d h⁻¹ * determinantWeight c ((((1 : ℕ) : ℂ) + 1) / 2) h *
        columnGaussian p q (rowPoint h.val k) ∂D.groupHaar) = _
  simp only [Nat.cast_one, show ((1 : ℂ) + 1) / 2 = 1 by norm_num]
  have hF (h : H) : characterVector d h⁻¹ * determinantWeight c 1 h * columnGaussian p q (rowPoint h.val k) =
      angularValue p q k * (characterVector d h⁻¹ * determinantWeight c 1 h * gaussianPower (p.val + q.val) h.val.det) := by
    rw [columnGaussian_rowPoint p q h hk]
    ring
  simp_rw [hF]
  rw [integral_const_mul, radialMoment]
  ring

private theorem rankOneCharacter_dual (d : RealCharacterData) :
    ArchimedeanLocal.dualFunction 1 (characterVector d) = characterVector d.inverse := by
  funext g
  rw [RealRankZero.dualFunction_apply]
  change (d.character (GeneralLinear.determinant (GeneralLinear.inverseTranspose 1 ℝ g)) : ℂ) =
    (d.inverse.character (GeneralLinear.determinant g) : ℂ)
  rw [Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose]
  change (d.character (GeneralLinear.determinant g)⁻¹ : ℂ) =
    (((d.character (GeneralLinear.determinant g))⁻¹ : ℂˣ) : ℂ)
  rw [map_inv]

private theorem pairL_two_one (c d e : RealCharacterData) (s : ℂ) :
    ((realPairLFactor [.character c, .character d] [.character e]).denominator s)⁻¹ =
      Gammaℝ (s + (c.mul e).exponent + (c.mul e).parity.val) *
        Gammaℝ (s + (d.mul e).exponent + (d.mul e).parity.val) := by
  change ((realLFactor [.character (c.mul e), .character (d.mul e)]).denominator s)⁻¹ = _
  rw [realLFactor_cons, realLFactor_singleton, RealBlock.lFactor_character, RealBlock.lFactor_character,
    Langlands.LocalFactor.ReciprocalEntire.denominator_mul,
    Langlands.LocalFactor.ReciprocalEntire.denominator_shift,
    Langlands.LocalFactor.ReciprocalEntire.denominator_shift]
  change ((Gammaℝ _ )⁻¹ * (Gammaℝ _)⁻¹)⁻¹ = _
  rw [mul_inv_rev, inv_inv, inv_inv, add_assoc, add_assoc, mul_comm]

private def adjacentGaussianCoefficient (D : RealQuotientMeasureData 0)
    (c d : RealCharacterData) (p q : Fin 2) : G → ℂ :=
  realAdjacentGodementCoefficient (r := 0) D (-1) (columnGaussian p q) (characterVector d) c

private theorem adjacentGaussianCoefficient_eq_additiveJacquet (D : RealQuotientMeasureData 0)
    (c d : RealCharacterData) (p q : Fin 2) (hc : d.exponent.re < c.exponent.re) :
    adjacentGaussianCoefficient D c d p q =
      additiveJacquetIntegral (-1) (sectionValue D.groupHaar c (characterVector d) (columnGaussian p q)) := by
  have hDom : IsStrictlyDominant (realPositionExponent [.character c, .character d]) 1 := by
    intro j hj
    have : j = 0 := by omega
    subst j
    exact hc
  have hf : characterVector d ∈ principalSeries ℝ 1 (realPositionCharacter [.character d]) :=
    (Submodule.mem_inf.mp (characterVector_mem d)).1.1
  have hStrip (j : Fin (0 + 1)) : ((0 + 1 : ℕ) : ℝ) +
      normExponent (realPositionExponent [.character d]) (0 + 1) j ≤
      c.exponent.re + ((((0 + 1 : ℕ) : ℝ)) + 1) / 2 := by
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa [normExponent, realPositionExponent, add_comm] using hc.le
  funext g
  have h := (realGodementSchwartzJoint 0 D (-1) c [.character d] (characterVector d)
    hf hDom hStrip (columnGaussian p q) g).2
  rw [funext (additiveJacquetIntegral_rankOne (-1) (characterVector d))] at h
  exact h.symm

private theorem exists_adjacentGaussianIntegral_eq (D : RealQuotientMeasureData 0) (c d e : RealCharacterData) :
    ∃ C : ℂ, C ≠ 0 ∧ ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      realUnequalIntegral (Nat.lt_succ_self 0) D
        (adjacentGaussianCoefficient D c d (c.mul e).parity (d.mul e).parity) (characterVector e) s =
        C * ((realPairLFactor [.character c, .character d] [.character e]).denominator s)⁻¹ := by
  let U := characterVector d
  let V := characterVector e
  let F := matrixTateGaussian (c.mul e).parity
  let f₀ := rowTateGaussian (d.mul e).parity
  let f := realRowSchwartzFourier 1 1 f₀
  have hU : U ∈ realUniformWhittakerModel 0 [.character d] (-(-1 : ℝˣ)) :=
    rankOneCharacter_mem_uniform d (-1)
  have hUd : ArchimedeanLocal.dualFunction 1 U ∈ realUniformWhittakerModel 0 [.character d.inverse] (-1) := by
    rw [rankOneCharacter_dual]
    exact rankOneCharacter_mem_uniform d.inverse 1
  have hV : V ∈ realUniformWhittakerModel 0 [.character e] (-1) := rankOneCharacter_mem_uniform e 1
  obtain ⟨q, hq0, hq⟩ := exists_measure_eq D
  obtain ⟨k, hk0, hk⟩ := exists_groupHaar_eq D
  obtain ⟨σ, hOrd⟩ := realAdjacentGodementHalfPlane D (-1) c F f [.character d] [.character d.inverse]
    [.character e] U V hU hUd hV
  let C : ℂ := realAdjacentWeylSign 0 c * ((q : ℂ) * (k : ℂ))
  have hC : C ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
      (mul_ne_zero (by exact_mod_cast hq0) (by exact_mod_cast hk0))
  refine ⟨C, hC, max σ (max (-(c.mul e).exponent.re) (-(d.mul e).exponent.re)), fun s hs => ?_⟩
  have h₁ : 0 < (s + (c.mul e).exponent).re := by
    have h := (le_max_left (-(c.mul e).exponent.re) _).trans_lt ((le_max_right σ _).trans_lt hs)
    rw [Complex.add_re]
    linarith
  have h₂ : 0 < (s + (d.mul e).exponent).re := by
    have h := (le_max_right _ (-(d.mul e).exponent.re)).trans_lt ((le_max_right σ _).trans_lt hs)
    rw [Complex.add_re]
    linarith
  have hFt : realRowSchwartzFourier 1 (-1) f = f₀ := realRowSchwartzFourier_neg_comp 1 1 f₀
  have hZ := (hOrd s ((le_max_left _ _).trans_lt hs)).1
  change realUnequalIntegral _ D (adjacentGaussianCoefficient D c d (c.mul e).parity (d.mul e).parity) V s =
    realAdjacentWeylSign 0 c * realAdjacentUnfoldedIntegral D c.character.toMonoidHom F
      (realRowSchwartzFourier 1 (-1) f) U V s at hZ
  rw [hZ, hFt, realAdjacentUnfoldedIntegral_gaussians D c d e hq hk s h₁ h₂, pairL_two_one]
  dsimp only [C]
  ring

private theorem radialMoment_ne_zero (D : RealQuotientMeasureData 0) (c d e : RealCharacterData)
    (hc : d.exponent.re < c.exponent.re) :
    radialMoment D c d ((c.mul e).parity.val + (d.mul e).parity.val) ≠ 0 := by
  let p := (c.mul e).parity
  let q := (d.mul e).parity
  let v := sectionValue D.groupHaar c (characterVector d) (columnGaussian p q)
  have hv : v ∈ Automorphic.realStandardKFinite 2 [.character c, .character d] :=
    gaussianColumnSection_mem D c d hc.le p q
  intro h0
  have hV : v = 0 := by
    apply eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact hv.1.1
    intro k hk
    rw [show v k = _ from gaussianColumnSection_angular D c d p q hk, h0, zero_mul]
  have hW : adjacentGaussianCoefficient D c d p q = 0 := by
    rw [adjacentGaussianCoefficient_eq_additiveJacquet D c d p q hc, show
      sectionValue D.groupHaar c (characterVector d) (columnGaussian p q) = 0 from hV]
    ext g
    simp [additiveJacquetIntegral, additiveJacquetKernel]
  obtain ⟨C, hC, b, hb⟩ := exists_adjacentGaussianIntegral_eq D c d e
  let L := realPairLFactor [.character c, .character d] [.character e]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ s : ℂ, a < s.re → L.denominator s ≠ 0 :=
    ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks _ _)
  let s : ℂ := (max a b + 1 : ℝ)
  have hs₁ : a < s.re := by dsimp only [s]; rw [ofReal_re]; linarith [le_max_left a b]
  have hs₂ : b < s.re := by dsimp only [s]; rw [ofReal_re]; linarith [le_max_right a b]
  have h := hb s hs₂
  change realUnequalIntegral _ D (adjacentGaussianCoefficient D c d p q) (characterVector e) s =
    C * (L.denominator s)⁻¹ at h
  rw [hW] at h
  have hZero : realUnequalIntegral (Nat.lt_succ_self 0) D 0 (characterVector e) s = 0 := by
    simp [realUnequalIntegral, ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.unequalIntegrand]
  exact (mul_ne_zero hC (inv_ne_zero (ha s hs₁))) (h.symm.trans hZero)

private theorem determinantWeight_compact_charData (p : Fin 2) (z w : ℂ) {k : G}
    (hk : k ∈ unitaryCompact ℝ 2) :
    determinantWeight (charData p z) (1 / 2) k = determinantWeight (charData p w) (1 / 2) k := by
  let u := GeneralLinear.determinant k
  have hu : |(u : ℝ)| = 1 := MaximalParabolicIntegration.abs_det_unitary ⟨k, hk⟩
  change ((charData p z).character u : ℂ) * ((|(u : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
    ((charData p w).character u : ℂ) * ((|(u : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ)
  rw [(charData p z).character_eq, (charData p w).character_eq, hu]
  simp [charData]

private theorem characterList_two (p : Fin 2) (d : RealCharacterData) (z : ℂ) :
    characterList (![p, d.parity] : Fin 2 → Fin 2) (![z, d.exponent] : Fin 2 → ℂ) =
      [.character (charData p z), .character d] := by
  simp [characterList, List.ofFn_succ, RealCharacterCrossing.charData_eta]

private theorem adjacentGaussianCoefficient_mem_closedChamber (D : RealQuotientMeasureData 0)
    (c d e : RealCharacterData) (hc : d.exponent.re ≤ c.exponent.re) :
    adjacentGaussianCoefficient D c d (c.mul e).parity (d.mul e).parity ∈
      realUniformWhittakerModel 1 [.character c, .character d] 1 := by
  let p := c.parity
  let k₀ : Fin 2 := (c.mul e).parity
  let k₁ : Fin 2 := (d.mul e).parity
  let l : Fin 2 → Fin 2 := ![p, d.parity]
  let exponents (z : ℂ) : Fin 2 → ℂ := ![z, d.exponent]
  let z₀ := d.exponent + 1
  let c₀ := charData p z₀
  have hc₀ : d.exponent.re < z₀.re := by simp [z₀, add_re]
  have hl (z : ℂ) : characterList l (exponents z) = [.character (charData p z), .character d] :=
    characterList_two p d z
  let v (z : ℂ) := sectionValue D.groupHaar (charData p z) (characterVector d) (columnGaussian k₀ k₁)
  have hv (z : ℂ) (hz : d.exponent.re ≤ z.re) :
      v z ∈ Automorphic.realStandardKFinite 2 (characterList l (exponents z)) := by
    rw [hl]
    exact gaussianColumnSection_mem D (charData p z) d hz k₀ k₁
  let φ := compactRestriction (v z₀)
  have hφ : IsCompactProfile l φ := isCompactProfile_compactRestriction (hv z₀ hc₀.le)
  let moment (z : ℂ) := radialMoment D (charData p z) d (k₀.val + k₁.val)
  have hM₀ : moment z₀ ≠ 0 := radialMoment_ne_zero D c₀ d e hc₀
  let C (z : ℂ) := moment z / moment z₀
  have hK (z : ℂ) (k : G) (hk : k ∈ unitaryCompact ℝ 2) : v z k = C z * v z₀ k := by
    rw [show v z k = moment z * (determinantWeight (charData p z) (1 / 2) k * angularValue k₀ k₁ k)
      from gaussianColumnSection_angular D _ _ _ _ hk,
      show v z₀ k = moment z₀ * (determinantWeight (charData p z₀) (1 / 2) k * angularValue k₀ k₁ k)
      from gaussianColumnSection_angular D _ _ _ _ hk,
      determinantWeight_compact_charData p z z₀ hk]
    simp only [C, ← mul_assoc, div_mul_cancel₀ _ hM₀]
  have hSection (z : ℂ) (hz : d.exponent.re ≤ z.re) : v z = C z • standardSection (exponents z) φ := by
    have hs : C z • standardSection (exponents z) φ ∈
        Automorphic.realStandardKFinite 2 (characterList l (exponents z)) :=
      Submodule.smul_mem _ _ (standardSection_mem hφ (exponents z))
    apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries (hv z hz).1.1 hs.1.1
    intro k hk
    let κ : Matrix.unitaryGroup (Fin 2) ℝ := ⟨k.val, hk⟩
    have hκ : Unitary.toUnits κ = k := Units.ext rfl
    have hφeq := congrFun (compactRestriction_standardSection φ (exponents z)) κ
    change standardSection (exponents z) φ (Unitary.toUnits κ) = v z₀ (Unitary.toUnits κ) at hφeq
    rw [hκ] at hφeq
    rw [Pi.smul_apply, smul_eq_mul, hφeq]
    exact hK z _ hk
  let W (z : ℂ) := adjacentGaussianCoefficient D (charData p z) d k₀ k₁
  let J (z : ℂ) := canonicalJacquetFamily (-1) hφ (exponents z)
  have hW_eq (z : ℂ) (hz : d.exponent.re < z.re) : W z = C z • J z := by
    have hCh : exponents z ∈ realSpectralChamber 1 := by
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hz
    let K := canonicalJacquetMap (-1) l (exponents z)
    let f : Automorphic.realStandardKFinite 2 (characterList l (exponents z)) :=
      ⟨standardSection (exponents z) φ, standardSection_mem hφ (exponents z)⟩
    have hKf : K f = J z := canonicalJacquetMap_standardSection (-1) hφ (exponents z)
    rw [← hKf, ← map_smul]
    change W z = canonicalJacquetMap (-1) l (exponents z) (C z • f)
    rw [canonicalJacquetMap_agrees (-1) l hCh]
    exact (adjacentGaussianCoefficient_eq_additiveJacquet D _ d k₀ k₁ hz).trans
      (congrArg (additiveJacquetIntegral (-1)) (hSection z hz.le))
  have heq : W c.exponent = C c.exponent • J c.exponent := by
    funext g
    have hWc : ContinuousAt (fun z => W z g) c.exponent :=
      (differentiable_godementLeadingFamily D (-1) (columnGaussian k₀ k₁)
        (show characterVector d ∈ realUniformWhittakerModel 0 [.character d] (-(-1 : ℝˣ)) from
          rankOneCharacter_mem_uniform d (-1)) p g).continuous.continuousAt
    have hExponents : Continuous exponents := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_id
      · exact continuous_const
    have hJ : Continuous (fun z => J z g) :=
      ((canonicalJacquetFamily_properties (-1) hφ).2.2.1 [] g).continuous.comp hExponents
    have hC : ContinuousAt C c.exponent := (continuousAt_radialMoment D p d _ hc).div_const _
    have hRight : ContinuousAt (fun z => C z * J z g) c.exponent :=
      hC.mul hJ.continuousAt
    let step (x : ℝ) := c.exponent + (x : ℂ)
    have hStep : Tendsto step (𝓝[>] (0 : ℝ)) (𝓝 c.exponent) := by
      have ht : ContinuousAt step 0 := (continuous_const.add Complex.continuous_ofReal).continuousAt
      have h0 : step 0 = c.exponent := by simp [step]
      rw [← h0]
      exact ht.tendsto.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique_of_eventuallyEq (hWc.tendsto.comp hStep) (hRight.tendsto.comp hStep) ?_
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with x hx
    have hs : d.exponent.re < (step x).re := by
      change 0 < x at hx
      simp only [step, add_re, ofReal_re]
      linarith
    exact congrFun (hW_eq (step x) hs) g
  have hJmem : J c.exponent ∈ realUniformWhittakerModel 1 (characterList l (exponents c.exponent)) 1 := by
    rw [show (1 : ℝˣ) = -(-1 : ℝˣ) by simp, show J c.exponent =
      canonicalJacquetMap (-1) l (exponents c.exponent)
        ⟨standardSection (exponents c.exponent) φ, standardSection_mem hφ (exponents c.exponent)⟩
        from (canonicalJacquetMap_standardSection (-1) hφ _).symm]
    exact canonicalJacquetMap_mem_uniformModel (-1) l _ _
  rw [hl, RealCharacterCrossing.charData_eta c] at hJmem
  have hMem := Submodule.smul_mem _ (C c.exponent) hJmem
  rw [← heq] at hMem
  simpa only [W, p, RealCharacterCrossing.charData_eta c] using hMem

/-- At real ranks two and one in the closed two-character chamber, one ordinary test
at the standard scale realizes the pair L-factor on a right half-plane. -/
def RealAdjacentRankOneClosedChamberStatement : Prop :=
  ∀ (c d e : RealCharacterData), d.exponent.re ≤ c.exponent.re →
    ∀ D : RealQuotientMeasureData 0,
    HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest (Nat.lt_succ_self 0) [.character c, .character d] [.character e] 1 D)
      (realPairLFactor [.character c, .character d] [.character e])

theorem realAdjacentRankOneClosedChamber : RealAdjacentRankOneClosedChamberStatement := by
  intro c d e hc D
  let V := characterVector e
  let W := adjacentGaussianCoefficient D c d (c.mul e).parity (d.mul e).parity
  have hW : W ∈ realWhittakerModel 1 [.character c, .character d] 1 :=
    RealUniformWhittaker.model_le_model _ _ (adjacentGaussianCoefficient_mem_closedChamber D c d e hc)
  have hV : V ∈ realWhittakerModel 0 [.character e] (-1) :=
    RealUniformWhittaker.model_le_model _ _ (rankOneCharacter_mem_uniform e 1)
  obtain ⟨C, hC, b, hb⟩ := exists_adjacentGaussianIntegral_eq D c d e
  let i : realWhittakerModel 1 [.character c, .character d] 1 ×
      realWhittakerModel 0 [.character e] (-1) := (⟨C⁻¹ • W, Submodule.smul_mem _ _ hW⟩, ⟨V, hV⟩)
  let L := realPairLFactor [.character c, .character d] [.character e]
  refine ⟨1, fun _ => i, fun _ => ⟨fun _ => 1, fun _ _ => analyticAt_const, ?_⟩, fun s => by simp⟩
  refine ⟨b, fun s hs => ?_⟩
  change realUnequalIntegral (Nat.lt_succ_self 0) D (C⁻¹ • W) V s = 1 * (L.denominator s)⁻¹
  have hSmul : realUnequalIntegral (Nat.lt_succ_self 0) D (C⁻¹ • W) V s =
      C⁻¹ * realUnequalIntegral (Nat.lt_succ_self 0) D W V s := by
    simp only [realUnequalIntegral, ArchimedeanLocal.unequalIntegral, ArchimedeanLocal.unequalIntegrand,
      Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [hSmul, hb s hs, ← mul_assoc, inv_mul_cancel₀ hC]

/-- At real ranks two and one, for a strictly dominant two-character list, one
ordinary test at the standard scale realizes the pair L-factor on a right half-plane. -/
def RealAdjacentRankOneGenerationStatement : Prop :=
  ∀ (c d e : RealCharacterData), d.exponent.re < c.exponent.re →
    ∀ D : RealQuotientMeasureData 0,
    HasFiniteOrdinaryNormalizationSum
      (realOrdinaryUnequalTest (Nat.lt_succ_self 0) [.character c, .character d] [.character e] 1 D)
      (realPairLFactor [.character c, .character d] [.character e])

theorem realAdjacentRankOneGeneration : RealAdjacentRankOneGenerationStatement := by
  intro c d e hc D
  exact realAdjacentRankOneClosedChamber c d e hc.le D

end Langlands.Global.RankinSelbergGlobal.RealAdjacentRankOne
