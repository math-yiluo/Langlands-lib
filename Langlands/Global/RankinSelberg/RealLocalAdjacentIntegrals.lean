import Langlands.Global.RankinSelberg.RealUnequalPairConvergence

/-! # The real corank-one dual integral has no rectangular integration -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r : ℕ}

local notation "h" => Nat.lt_succ_self r
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "R" => Matrix (Fin (r + 1 - (r + 1))) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ
local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Wd" => ArchimedeanLocal.dualFunction (r + 2)
local notation "Vd" => ArchimedeanLocal.dualFunction (r + 1)

private theorem adjacentRectangularPoint (g : H) (x : R) :
    ArchimedeanLocal.rectangularPoint h g x = padGL (Nat.succ_le_succ (Nat.le_succ r)) g := by
  have hx : x = 0 := by
    ext i j
    exact Fin.elim0 (Fin.cast (Nat.sub_self (r + 1)) i)
  rw [hx, RealUnequalPairConvergence.rectangularPoint_zero]

private theorem adjacentUnfoldingWeyl : ArchimedeanLocal.unfoldingWeyl (K := ℝ) h = 1 := by
  have hw (n : ℕ) (hn : n = 1) : weylLong n ℝ = 1 := by
    subst n
    apply Units.ext
    ext i j
    change weylLong 1 ℝ i j = (1 : Matrix (Fin 1) (Fin 1) ℝ) i j
    rw [weylLong_entry, Matrix.one_apply]
    simp [Subsingleton.elim j.rev i, Subsingleton.elim i j]
  unfold ArchimedeanLocal.unfoldingWeyl
  rw [hw _ (by omega)]
  change reindex _ (blockSum 1) = 1
  simp only [map_one]

private theorem rectangularMeasure_eq_dirac (a : ℝˣ) (m n : ℕ) (hm : m = 0) :
    rectangularMeasure (realSelfDualMeasure a) m n = Measure.dirac 0 := by
  subst m
  exact RankinSelberg.rectangularMeasure_zero_rows _ _

/-- The corank-one dual block kernel is the ordinary kernel of the pointwise duals. -/
theorem realUnequalDualKernel_adjacent (W : G → ℂ) (V : H → ℂ) (s : ℂ) (p : Q × R) :
    realUnequalDualKernel h W V s p = realUnequalIntegrand h (Wd W) (Vd V) s p.1 := by
  simp only [realUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
    realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    adjacentRectangularPoint, adjacentUnfoldingWeyl, mul_one]

/-- The product measure of the corank-one dual kernel is the pushforward by
adjoining the unique empty rectangle. -/
theorem realUnequalDualMeasure_adjacent (a : ℝˣ) (D : RealQuotientMeasureData r) :
    realUnequalDualMeasure (r := r + 1) a D = Measure.map (fun q : Q => (q, (0 : R))) D.measure := by
  let : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
  let : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℝ))
  let : SecondCountableTopology H := Units.isInducing_embedProduct.secondCountableTopology
  let : SigmaCompactSpace Q := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ)
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr hq.surjective]
    exact isSigmaCompact_range hq.continuous
  let := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  rw [realUnequalDualMeasure, rectangularMeasure_eq_dirac a _ _ (Nat.sub_self _), Measure.prod_dirac]

/-- Absolute integrability of the corank-one dual kernel is equivalent to that of the
ordinary integrand of the pointwise duals. -/
theorem integrable_realUnequalDualKernel_adjacent_iff
    (a : ℝˣ) (D : RealQuotientMeasureData r) (W : G → ℂ) (V : H → ℂ) (s : ℂ) :
    Integrable (realUnequalDualKernel h W V s) (realUnequalDualMeasure (r := r + 1) a D) ↔
      Integrable (realUnequalIntegrand h (Wd W) (Vd V) s) D.measure := by
  rw [realUnequalDualMeasure_adjacent, (measurableEmbedding_prod_mk_right (0 : R)).integrable_map_iff]
  rw [show (realUnequalDualKernel h W V s ∘ fun q : Q => (q, (0 : R))) =
      realUnequalIntegrand h (Wd W) (Vd V) s from
    funext fun q => realUnequalDualKernel_adjacent W V s (q, 0)]

/-- The actual corank-one dual integral is the ordinary integral of the pointwise duals
with the original quotient measure and no extra scalar. -/
def RealUnequalDualIntegralAdjacentStatement (r : ℕ) : Prop :=
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℝ → ℂ)
    (V : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (s : ℂ),
    realUnequalDualIntegral (Nat.lt_succ_self r) a D W V s =
      realUnequalIntegral (Nat.lt_succ_self r) D
        (ArchimedeanLocal.dualFunction (r + 2) W) (ArchimedeanLocal.dualFunction (r + 1) V) s

theorem realUnequalDualIntegral_adjacent : RealUnequalDualIntegralAdjacentStatement r := by
  intro a D W V s
  simp only [realUnequalDualIntegral, blockIntegral,
    rectangularMeasure_eq_dirac a _ _ (Nat.sub_self _), integral_dirac,
    realUnequalIntegral, ArchimedeanLocal.unequalIntegral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
    realUnequalDualKernel_adjacent W V s (q, 0))

end Langlands.Global.RankinSelbergGlobal.RealJacquet
