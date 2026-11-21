import Langlands.Global.RankinSelberg.RealBorelAverageContinuity
import Langlands.Global.RankinSelberg.RealBorelRightHaar
import Langlands.Global.RankinSelberg.RealPrincipalSeriesCoefficientGrowth
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-! # The test distribution of a real principal-series Whittaker functional -/

noncomputable section

open Set TopologicalSpace MeasureTheory Langlands.Archimedean Langlands.GeneralLinear
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open scoped ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesDistribution

open RealBruhatDistributionRestriction RealBorelTestAverage RealBorelRightHaar
open RealBorelAverageContinuity RealWhittakerTranslationDistribution RealJacquetFrobenius

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "TestC" => 𝓓(invertibleDomain r, ℂ)
local notation "TestR" => 𝓓(invertibleDomain r, ℝ)

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance (L : Compacts G) : CompactSpace (L : Set G) :=
  isCompact_iff_compactSpace.mp L.isCompact

/-- The character blocks whose normalized inducing character has exponents `s`. -/
abbrev normalizedCharacterBlocks {n : ℕ} (s : Fin n → ℂ) (e : Fin n → Fin 2) :
    List RealBlock := (List.ofFn (chars s e)).map RealBlock.character

private theorem diagonal_ne_zero (b : B) (j : Fin (r + 1)) : b.val.val j j ≠ 0 :=
  diag_ne_zero b.property b.val.isUnit j

/-- The unit-valued normalized inducing character of the actual Borel. -/
def positionBorelCharacter (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) : B →* ℂˣ where
  toFun b := Units.mk0 (diagChar s e b.val.val)
    (Finset.prod_ne_zero_iff.mpr fun j _ => charFun_ne_zero (e j) (s j) (diagonal_ne_zero b j))
  map_one' := Units.ext (diagChar_one s e)
  map_mul' b c := Units.ext (diagChar_mul s e b.property c.property)

@[simp]
theorem positionBorelCharacter_val (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) (b : B) :
    (positionBorelCharacter s e b : ℂ) = diagChar s e b.val.val := rfl

theorem continuous_positionBorelCharacter (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) :
    Continuous (positionBorelCharacter s e) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun b : B => diagChar s e b.val.val)
  refine continuous_iff_continuousAt.mpr fun b => ?_
  have hb : ContinuousAt (fun c : B => c.val.val) b :=
    (Units.continuous_val.comp continuous_subtype_val).continuousAt
  exact ContinuousAt.comp' (f := fun c : B => c.val.val) (x := b)
    (contDiffAt_diagChar s e (diagonal_ne_zero b)).continuousAt hb

@[simp]
theorem positionBorelCharacter_unipotent (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) (u : U) :
    positionBorelCharacter s e (unipotentInBorel u) = 1 :=
  Units.ext (diagChar_of_diag_eq_one s e u.property.2)

/-- The diagonal-then-unipotent factor as an element of the actual Borel. -/
def diagonalUnipotentInBorel (d : Fin (r + 1) → ℝˣ) (u : U) : B :=
  ⟨Iwasawa.diagonalUnits d * u.val,
    mul_mem (diagonalUnits_mem_upperTriangular _ d) (upperUnipotent_le_upperTriangular _ _ u.property)⟩

theorem positionBorelCharacter_diagonalUnipotent (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2)
    (d : Fin (r + 1) → ℝˣ) (u : U) :
    (positionBorelCharacter s e (diagonalUnipotentInBorel d u) : ℂ) =
      principalSeriesCharacter ℝ (r + 1) (posChar s e) d := by
  rw [positionBorelCharacter_val, principalSeriesCharacter_eq]
  change diagChar s e ((Iwasawa.diagonalUnits d).val * u.val.val) = _
  rw [diagChar_mul s e (diagonalUnits_mem_upperTriangular _ d) u.property.1,
    diagChar_of_diag_eq_one s e u.property.2, mul_one, Iwasawa.diagonalUnits_val]

variable (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2)
local notation "P" => principalSeries ℝ (r + 1) (posChar s e)
local notation "ds" => normalizedCharacterBlocks s e
local notation "χ" => positionBorelCharacter s e
local notation "μ" => rightBorelMeasure r

private theorem continuous_weight : Continuous (inverseWeight χ) :=
  continuous_inverseWeight χ (continuous_positionBorelCharacter s e)

private def averageSection (f : TestC) : P := by
  refine ⟨fun g => borelAverage μ (inverseWeight χ) f g.val,
    contMDiff_borelAverage μ (continuous_weight s e) f, fun d u g => ?_⟩
  change borelAverage μ (inverseWeight χ) f ((diagonalUnipotentInBorel d u).val.val * g.val) = _
  rw [borelAverage_left_covariance, positionBorelCharacter_diagonalUnipotent]

/-- Borel averaging sends complex matrix tests linearly to smooth inducing sections. -/
def averageMap : TestC →ₗ[ℂ] P where
  toFun := averageSection s e
  map_add' f h := Subtype.ext (funext fun g => borelAverage_add μ (continuous_weight s e) f h g.val)
  map_smul' c f := Subtype.ext (funext fun g => borelAverage_smul μ (inverseWeight χ) c f g.val)

@[simp]
theorem averageMap_apply (f : TestC) (g : G) :
    (averageMap s e f : G → ℂ) g = borelAverage μ (inverseWeight χ) f g.val := rfl

private def compactUnitary (r : ℕ) : Compacts (Langlands.GeneralLinear (r + 1) ℝ) :=
  ⟨unitaryCompact ℝ (r + 1), isCompact_iff_compactSpace.mpr
    (RealPrincipalSeriesDuality.compactSpace_unitaryCompact (r + 1))⟩

/-- A compact-derivative-bounded functional composed with Borel averaging
is continuous on complex matrix tests. -/
def averagedFunctional (ℓ : P →ₗ[ℂ] ℂ) (hℓ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) :
    TestC →L[ℂ] ℂ := by
  let R := ℓ.comp (averageMap s e)
  refine ⟨R, continuous_of_continuousAt_zero R (Metric.continuousAt_iff'.mpr fun ε hε => ?_)⟩
  obtain ⟨m, Xs, A, _, hB⟩ := hℓ
  let L := compactUnitary r
  let Pj (j : Fin m) : TestC →L[ℝ] C((L : Set G), ℂ) :=
    ((averageOnCompactCLM μ (continuous_weight s e) L).restrictScalars ℝ).comp
      (rightDerivativeWordTestCLM (Xs j))
  have hBound (f : TestC) : ‖R f‖ ≤ A * ∑ j, ‖Pj j f‖ := by
    apply hB
    intro j k hk
    change ‖RealLocalWhittaker.iteratedRightDerivative r (Xs j)
      (fun g => borelAverage μ (inverseWeight χ) f g.val) k‖ ≤ _
    rw [iteratedRightDerivative_borelAverage μ (continuous_weight s e)]
    exact (Pj j f).norm_coe_le_norm ⟨k, hk⟩
  have hc : Continuous (fun f : TestC => A * ∑ j, ‖Pj j f‖) :=
    continuous_const.mul (continuous_finsetSum _ fun j _ => (Pj j).continuous.norm)
  have h0 : A * ∑ j, ‖Pj j 0‖ = 0 := by
    simp only [map_zero, norm_zero, Finset.sum_const_zero, mul_zero]
  have hn := hc.continuousAt.eventually_lt continuousAt_const (h0 ▸ hε)
  filter_upwards [hn] with f hf
  rw [map_zero R, dist_zero_right]
  exact (hBound f).trans_lt hf

/-- The distribution on real tests attached to a continuous inducing functional. -/
def averagedDistribution (ℓ : P →ₗ[ℂ] ℂ) (hℓ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) :
    𝓓'(invertibleDomain r, ℂ) :=
  ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℂ {S : Set TestR | IsCompact S}
    (((averagedFunctional s e ℓ hℓ).restrictScalars ℝ).comp (TestFunction.postcompCLM Complex.ofRealCLM))

theorem averagedDistribution_apply (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ) (f : TestR) :
    averagedDistribution s e ℓ hℓ f = ℓ (averageMap s e (TestFunction.postcompCLM Complex.ofRealCLM f)) := rfl

/-- The actual unipotent equivariance of the inducing functional gives both
unipotent transformation laws on its distribution. -/
theorem averagedDistribution_covariant (a : ℝˣ) (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : RealPrincipalSeries.HasCompactDerivativeBound r ds ℓ)
    (hψ : ∀ (u : U) (F : P),
      ℓ (RealPrincipalSeries.translate r ds u.val F) = realWhittakerCharacter a u.val * ℓ F) :
    IsUnipotentWhittakerCovariant (averagedDistribution s e ℓ hℓ) a := by
  constructor
  · intro u f
    simp only [averagedDistribution_apply]
    congr 1
    apply Subtype.ext
    funext g
    have hfg : ∀ X, TestFunction.postcompCLM Complex.ofRealCLM (leftTranslateTest u.val f) X =
        TestFunction.postcompCLM Complex.ofRealCLM f ((unipotentInBorel u).val.val * X) :=
      fun _ => rfl
    rw [averageMap_apply, averageMap_apply,
      borelAverage_left_pullback μ χ _ _ (unipotentInBorel u) (map_left_unipotent_rightBorelMeasure u) hfg,
      positionBorelCharacter_unipotent, Units.val_one, one_mul]
  · intro u f
    let F := averageMap s e (TestFunction.postcompCLM Complex.ofRealCLM f)
    change ℓ (averageMap s e (TestFunction.postcompCLM Complex.ofRealCLM (rightTranslateTest u.val f))) =
      realWhittakerCharacter a u.val * ℓ F
    rw [← hψ u F]
    apply congrArg ℓ
    apply Subtype.ext
    funext g
    change borelAverage μ (inverseWeight χ)
      (TestFunction.postcompCLM Complex.ofRealCLM (rightTranslateTest u.val f)) g.val =
      borelAverage μ (inverseWeight χ) (TestFunction.postcompCLM Complex.ofRealCLM f) (g * u.val).val
    rw [Units.val_mul]
    exact borelAverage_right_pullback μ (inverseWeight χ) _ _ u.val (fun _ => rfl) g.val

/-- A compact-derivative-bounded equivariant form on the real character
principal series gives a distribution with the required Whittaker covariance. -/
def RealPrincipalSeriesDistributionStatement : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → ℂ) (e : Fin (r + 1) → Fin 2) (a : ℝˣ)
    (ℓ : principalSeries ℝ (r + 1) (posChar s e) →ₗ[ℂ] ℂ)
    (hℓ : RealPrincipalSeries.HasCompactDerivativeBound r (normalizedCharacterBlocks s e) ℓ),
    (∀ (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
      (F : principalSeries ℝ (r + 1) (posChar s e)),
      ℓ (RealPrincipalSeries.translate r (normalizedCharacterBlocks s e) u.val F) =
        realWhittakerCharacter a u.val * ℓ F) →
    IsUnipotentWhittakerCovariant (averagedDistribution s e ℓ hℓ) a

theorem realPrincipalSeriesDistribution : RealPrincipalSeriesDistributionStatement :=
  fun _ => averagedDistribution_covariant

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeriesDistribution
