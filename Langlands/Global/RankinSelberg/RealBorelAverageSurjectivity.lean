import Langlands.Global.RankinSelberg.RealPrincipalSeriesDistribution
import Langlands.Representation.Archimedean.MatrixTestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Surjectivity of real Borel averaging -/

noncomputable section

open Function Set TopologicalSpace MeasureTheory Metric
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealBorelAverageSurjectivity

open RealBruhatDistributionRestriction RealBorelTestAverage RealBorelRightHaar
open RealPrincipalSeriesDistribution RealJacquetFrobenius

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "TestC" => 𝓓(invertibleDomain r, ℂ)
local notation "TestR" => 𝓓(invertibleDomain r, ℝ)
local notation "μ" => rightBorelMeasure r

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩

private def squareGram (X : M) : M := X * X.transpose

private theorem contDiff_squareGram : ContDiff ℝ ∞ (squareGram (r := r)) :=
  contDiff_id.mul
    (Matrix.transposeLinearEquiv (Fin (r + 1)) (Fin (r + 1)) ℝ ℝ).toContinuousLinearEquiv.contDiff

private theorem isCompact_squareGram_preimage {S : Set M} (hS : IsCompact S) :
    IsCompact (squareGram ⁻¹' S : Set M) := by
  have hTrace : Continuous (Matrix.trace : M → ℝ) :=
    (Matrix.traceLinearMap (Fin (r + 1)) ℝ ℝ).toContinuousLinearMap.continuous
  obtain ⟨A, hA⟩ := hS.bddAbove_image hTrace.continuousOn
  let R := |A| + 1
  apply ((isCompact_Icc : IsCompact (Icc (-R) R)).matrix).of_isClosed_subset
    (hS.isClosed.preimage contDiff_squareGram.continuous)
  intro X hX i j
  have hd (a : Fin (r + 1)) : squareGram X a a = ∑ b, X a b ^ 2 := by
    simp only [squareGram, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hdiag : squareGram X i i ≤ (squareGram X).trace :=
    Finset.single_le_sum (fun a _ => hd a ▸ Finset.sum_nonneg (fun b _ => sq_nonneg (X a b)))
      (Finset.mem_univ i)
  have hsq : X i j ^ 2 ≤ squareGram X i i := by
    rw [hd]
    exact Finset.single_le_sum (fun b _ => sq_nonneg (X i b)) (Finset.mem_univ j)
  apply abs_le_of_sq_le_sq' _ (by positivity : 0 ≤ R)
  calc
    X i j ^ 2 ≤ (squareGram X).trace := hsq.trans hdiag
    _ ≤ A := hA (mem_image_of_mem _ hX)
    _ ≤ |A| := le_abs_self A
    _ ≤ R ^ 2 := by dsimp [R]; nlinarith [abs_nonneg A, sq_nonneg |A|]

private theorem squareGram_mul_unitary (g : G) {k : G} (hk : k ∈ unitaryCompact ℝ (r + 1)) :
    squareGram (g * k).val = squareGram g.val := by
  simp only [squareGram, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc k.val k.val.transpose, GramFormula.mul_transpose_eq_one_of_mem hk, one_mul]

private theorem exists_rightUnitaryCutoff :
    ∃ κ : G → ℝ, ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℝ) ∞ κ ∧
      HasCompactSupport κ ∧ 0 ≤ κ ∧ κ 1 = 1 ∧
      ∀ (g k : G), k ∈ unitaryCompact ℝ (r + 1) → κ (g * k) = κ g := by
  have hOpen : IsOpen {X : M | IsUnit X} := isOpen_setOf_isUnit_matrix
  obtain ⟨δ, hδ, hδU⟩ := nhds_basis_closedBall.mem_iff.mp
    (hOpen.mem_nhds (show (1 : M) ∈ {X : M | IsUnit X} from isUnit_one))
  let β : ContDiffBump (1 : M) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let κ : G → ℝ := fun g => β (squareGram g.val)
  refine ⟨κ, (β.contDiff.comp contDiff_squareGram).contMDiff.comp Units.contMDiff_val,
    ?_, fun _ => β.nonneg, ?_, fun g k hk => ?_⟩
  · let S : Set M := squareGram ⁻¹' closedBall 1 δ
    have hS : IsCompact S := isCompact_squareGram_preimage (isCompact_closedBall _ _)
    have hu (X : M) (hX : X ∈ S) : IsUnit X := by
      have h : IsUnit (squareGram X) := hδU hX
      rw [Matrix.isUnit_iff_isUnit_det] at h ⊢
      have hdet : IsUnit (X.det * X.transpose.det) := by
        simpa only [squareGram, Matrix.det_mul] using h
      exact isUnit_of_mul_isUnit_left hdet
    apply HasCompactSupport.of_support_subset_isCompact (RealGodement.isCompact_val_preimage hS hu)
    intro g hg
    by_contra h
    apply hg
    exact β.zero_of_le_dist (not_le.mp h).le
  · change β (squareGram (1 : G).val) = 1
    simp only [Units.val_one, squareGram, Matrix.transpose_one, mul_one]
    exact β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le)
  · change β (squareGram (g * k).val) = β (squareGram g.val)
    rw [squareGram_mul_unitary g hk]

variable (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2)
local notation "P" => principalSeries ℝ (r + 1) (posChar s e)
local notation "ds" => normalizedCharacterBlocks s e
local notation "χ" => positionBorelCharacter s e

private theorem inducingCharacter_one (u : U) :
    principalSeriesCharacter ℝ (r + 1) (posChar s e) 1 = 1 := by
  have h : diagonalUnipotentInBorel (1 : Fin (r + 1) → ℝˣ) u = unipotentInBorel u := by
    apply Subtype.ext
    change Iwasawa.diagonalUnits (1 : Fin (r + 1) → ℝˣ) * u.val = u.val
    rw [map_one, one_mul]
  rw [← positionBorelCharacter_diagonalUnipotent s e 1 u, h, positionBorelCharacter_unipotent,
    Units.val_one]

private theorem section_left_borel (F : P) (b : B) (g : G) :
    (F : G → ℂ) (b.val * g) = (χ b : ℂ) * (F : G → ℂ) g := by
  obtain ⟨⟨d, u⟩, rfl⟩ := (torusUnipotentHomeomorph (r := r)).surjective b
  have hb : torusUnipotentHomeomorph (d, u) = unipotentInBorel u * diagonalUnipotentInBorel d (1 : U) := by
    apply Subtype.ext
    rw [torusUnipotentHomeomorph_val]
    change u.val * Iwasawa.diagonalUnits d = u.val * (Iwasawa.diagonalUnits d * 1)
    rw [mul_one]
  rw [torusUnipotentHomeomorph_val, mul_assoc, hb, map_mul, positionBorelCharacter_unipotent, one_mul,
    positionBorelCharacter_diagonalUnipotent]
  have hu := F.property.2 1 u (Iwasawa.diagonalUnits d * g)
  rw [map_one, one_mul, inducingCharacter_one s e u, one_mul] at hu
  rw [hu]
  simpa only [Subgroup.coe_one, mul_one] using F.property.2 d 1 g

/-- Each smooth inducing section can be produced by averaging one compact matrix test. -/
theorem averageMap_surjective : Function.Surjective (averageMap s e) := by
  intro F
  obtain ⟨κ, hκ, hκS, hκNonneg, hκOne, hκRight⟩ := exists_rightUnitaryCutoff (r := r)
  let w : B → ℝ := fun b => κ b.val
  have hw : Continuous w := hκ.continuous.comp continuous_subtype_val
  have hwS : HasCompactSupport w := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isClosed_upperTriangularSubgroup (r + 1) ℝ).isClosedEmbedding_subtypeVal.isCompact_preimage hκS)
    exact fun b hb => subset_tsupport κ hb
  let Z : ℝ := ∫ b, w b ∂μ
  have hZ : 0 < Z := by
    apply hw.integral_pos_of_hasCompactSupport_nonneg_nonzero hwS (fun b => hκNonneg b.val) (x := (1 : B))
    change κ (1 : G) ≠ 0
    rw [hκOne]
    exact one_ne_zero
  let L : G → ℂ := fun g => (κ g : ℂ) * (F : G → ℂ) g
  have hL : ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ L :=
    RealPrincipalSeriesDuality.contMDiff_mul_fun
      (Complex.ofRealCLM.contDiff.contMDiff.comp hκ) F.property.1
  have hLS : HasCompactSupport L :=
    (hκS.comp_left Complex.ofReal_zero).mul_right
  let t := (matrixTestFunctionKernelEquiv (F := ℝ) (n := r + 1)).symm ⟨L, hL, hLS⟩
  let f : TestC := ⟨t, t.contDiff, t.hasCompactSupport, fun X hX => by
    obtain ⟨g, hg⟩ := t.tsupport_subset hX
    exact ⟨g, hg⟩⟩
  have hf (g : G) : f g.val = (κ g : ℂ) * (F : G → ℂ) g := unitsExtension_val L g
  have hEq (k : G) (hk : k ∈ unitaryCompact ℝ (r + 1)) :
      (averageMap s e f : G → ℂ) k = (Z : ℂ) * (F : G → ℂ) k := by
    rw [averageMap_apply, borelAverage]
    calc
      _ = ∫ b : B, (w b : ℂ) * (F : G → ℂ) k ∂μ := by
        apply integral_congr_ae
        filter_upwards with b
        rw [← Units.val_mul, hf (b.val * k), hκRight _ _ hk, section_left_borel s e F b k]
        have hχ : inverseWeight χ b * (χ b : ℂ) = 1 :=
          congrArg Units.val (inv_mul_cancel (χ b))
        change inverseWeight χ b * ((w b : ℂ) * ((χ b : ℂ) * (F : G → ℂ) k)) = _
        rw [mul_left_comm (inverseWeight χ b), ← mul_assoc (inverseWeight χ b), hχ, one_mul]
      _ = _ := by rw [integral_mul_const, integral_complex_ofReal]
  have hAvg : averageMap s e f = (Z : ℂ) • F := by
    apply Subtype.ext
    funext g
    obtain ⟨d, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
    change (averageMap s e f : G → ℂ) (Iwasawa.diagonalUnits d * u.val * k) =
      (Z : ℂ) * (F : G → ℂ) (Iwasawa.diagonalUnits d * u.val * k)
    rw [(averageMap s e f).property.2 d u k, F.property.2 d u k, hEq k hk]
    ring
  refine ⟨(Z : ℂ)⁻¹ • f, ?_⟩
  rw [map_smul, hAvg, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hZ.ne'), one_smul]

/-- The induced distribution determines the original compact-derivative-bounded form. -/
theorem eq_of_averagedDistribution_eq (ℓ₁ ℓ₂ : P →ₗ[ℂ] ℂ)
    (h₁ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ₁)
    (h₂ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ₂)
    (h : averagedDistribution s e ℓ₁ h₁ = averagedDistribution s e ℓ₂ h₂) : ℓ₁ = ℓ₂ := by
  ext F
  obtain ⟨f, rfl⟩ := averageMap_surjective s e F
  let fR : TestR := TestFunction.postcompCLM Complex.reCLM f
  let fI : TestR := TestFunction.postcompCLM Complex.imCLM f
  have hf : f = TestFunction.postcompCLM Complex.ofRealCLM fR +
      Complex.I • TestFunction.postcompCLM Complex.ofRealCLM fI := by
    ext X
    change f X = ((f X).re : ℂ) + Complex.I * ((f X).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (f X)).symm
  rw [hf, map_add, map_smul, map_add, map_add, map_smul, map_smul]
  exact congrArg₂ (fun z₁ z₂ : ℂ => z₁ + Complex.I * z₂)
    (congrArg (fun T : 𝓓'(invertibleDomain r, ℂ) => T fR) h)
    (congrArg (fun T : 𝓓'(invertibleDomain r, ℂ) => T fI) h)

/-- The Borel averaging map for each normalized real character series is surjective. -/
def RealBorelAverageSurjectivityStatement : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2),
    Function.Surjective (averageMap s e)

theorem realBorelAverageSurjectivity : RealBorelAverageSurjectivityStatement :=
  fun _ => averageMap_surjective

end Langlands.Global.RankinSelbergGlobal.RealBorelAverageSurjectivity
