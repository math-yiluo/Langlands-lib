import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Complex corank-one local integrals -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure)

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "h" => Nat.lt_succ_self r
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "R" => Matrix (Fin (r + 1 - (r + 1))) (Fin (r + 1)) ℂ
local notation "G" => Langlands.GeneralLinear (r + 2) ℂ
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Wd" => ArchimedeanLocal.dualFunction (r + 2)
local notation "Vd" => ArchimedeanLocal.dualFunction (r + 1)

private theorem rectangularPoint_zero {u t : ℕ} (htu : t < u)
    (g : Langlands.GeneralLinear (t + 1) ℂ) :
    ArchimedeanLocal.rectangularPoint htu g 0 = padGL (Nat.succ_le_succ htu.le) g := by
  have hpair : lowerBlockPair g (0 : Matrix (Fin (u - (t + 1))) (Fin (t + 1)) ℂ) 1 =
      rankInclusion (u - (t + 1)) g := Units.ext rfl
  unfold ArchimedeanLocal.rectangularPoint lowerBlockLocalization
  rw [hpair]
  exact Unfolding.reindex_rankInclusion_rankInclusion _ _ _

private theorem adjacentRectangularPoint (g : H) (x : R) :
    ArchimedeanLocal.rectangularPoint h g x = padGL (Nat.succ_le_succ (Nat.le_succ r)) g := by
  have hx : x = 0 := by
    ext i j
    exact Fin.elim0 (Fin.cast (Nat.sub_self (r + 1)) i)
  rw [hx, rectangularPoint_zero]

private theorem adjacentUnfoldingWeyl :
    ArchimedeanLocal.unfoldingWeyl (K := ℂ) h = 1 := by
  have hw (n : ℕ) (hn : n = 1) : weylLong n ℂ = 1 := by
    subst n
    apply Units.ext
    ext i j
    change weylLong 1 ℂ i j = (1 : Matrix (Fin 1) (Fin 1) ℂ) i j
    rw [weylLong_entry, Matrix.one_apply]
    simp [Subsingleton.elim j.rev i, Subsingleton.elim i j]
  unfold ArchimedeanLocal.unfoldingWeyl
  rw [hw _ (by omega)]
  change reindex _ (blockSum 1) = 1
  simp only [map_one]

private theorem rectangularMeasure_eq_dirac (a : ℂˣ) (m n : ℕ) (hm : m = 0) :
    rectangularMeasure (complexSelfDualMeasure a) m n = Measure.dirac 0 := by
  subst m
  exact RankinSelberg.rectangularMeasure_zero_rows _ _

/-- In corank one the dual block kernel is the ordinary kernel of the duals. -/
theorem complexUnequalDualKernel_adjacent (W : G → ℂ) (V : H → ℂ)
    (s : ℂ) (p : Q × R) :
    complexUnequalDualKernel h W V s p = complexUnequalIntegrand h (Wd W) (Vd V) s p.1 := by
  simp only [complexUnequalDualKernel, blockKernel, ArchimedeanLocal.translateFunction,
    complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    adjacentRectangularPoint, adjacentUnfoldingWeyl, mul_one]

/-- The rectangular measure of the corank-one dual integral has a single point of mass one. -/
theorem complexUnequalDualMeasure_adjacent (a : ℂˣ) (D : ComplexQuotientMeasureData r) :
    complexUnequalDualMeasure (r := r + 1) a D = Measure.map (fun q : Q => (q, (0 : R))) D.measure := by
  let : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℂ))
  let : SecondCountableTopology (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  let : LocallyCompactSpace (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
  let : SecondCountableTopology H := Units.isInducing_embedProduct.secondCountableTopology
  let : SigmaCompactSpace Q := by
    have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) ℂ)
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr hq.surjective]
    exact isSigmaCompact_range hq.continuous
  let := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  rw [complexUnequalDualMeasure, rectangularMeasure_eq_dirac a _ _ (Nat.sub_self _),
    Measure.prod_dirac]

/-- Absolute integrability of the corank-one dual kernel equals that of the ordinary
integrand of the two dual Whittaker functions. -/
theorem integrable_complexUnequalDualKernel_adjacent_iff
    (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W : G → ℂ) (V : H → ℂ) (s : ℂ) :
    Integrable (complexUnequalDualKernel h W V s) (complexUnequalDualMeasure (r := r + 1) a D) ↔
      Integrable (complexUnequalIntegrand h (Wd W) (Vd V) s) D.measure := by
  rw [complexUnequalDualMeasure_adjacent, (measurableEmbedding_prod_mk_right (0 : R)).integrable_map_iff]
  rw [show (complexUnequalDualKernel h W V s ∘ fun q : Q => (q, (0 : R))) =
      complexUnequalIntegrand h (Wd W) (Vd V) s from
    funext fun q => complexUnequalDualKernel_adjacent W V s (q, 0)]

/-- The corank-one dual integral is the ordinary integral of the duals, with the same
quotient measure and no additional scalar. -/
theorem complexUnequalDualIntegral_adjacent (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W : G → ℂ) (V : H → ℂ) (s : ℂ) :
    complexUnequalDualIntegral h a D W V s = complexUnequalIntegral h D (Wd W) (Vd V) s := by
  simp only [complexUnequalDualIntegral, blockIntegral, rectangularMeasure_eq_dirac a _ _ (Nat.sub_self _),
    integral_dirac, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral]
  exact integral_congr_ae (Filter.Eventually.of_forall fun q =>
    complexUnequalDualKernel_adjacent W V s (q, 0))

/-- Absolute convergence of an ordinary unequal-rank complex integral on an open set
implies holomorphy there. -/
theorem differentiableOn_complexUnequalIntegral_of_integrable {u t : ℕ} (htu : t < u)
    (D : ComplexQuotientMeasureData t) (W : Langlands.GeneralLinear (u + 1) ℂ → ℂ)
    (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ) {S : Set ℂ} (hS : IsOpen S)
    (hInt : ∀ s ∈ S, Integrable (complexUnequalIntegrand htu W V s) D.measure) :
    DifferentiableOn ℂ (complexUnequalIntegral htu D W V) S := by
  let A (q : LeftUnipotentQuotient t ℂ) :=
    W (padGL (Nat.succ_le_succ htu.le) q.out) * V q.out *
      Complex.exp (-(((u - t : ℕ) : ℂ) / 2) * (complexQuotientLogDet q : ℂ))
  have hEq (s : ℂ) (q : LeftUnipotentQuotient t ℂ) :
      complexUnequalIntegrand htu W V s q = A q * Complex.exp (s * (complexQuotientLogDet q : ℂ)) := by
    simp only [A, complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
      ArchimedeanLocal.detPower, complexQuotientLogDet_out, sub_mul, Complex.exp_sub, neg_mul,
      Complex.exp_neg, div_eq_mul_inv]
    ring
  have hFun : complexUnequalIntegral htu D W V =
      fun s => ∫ q, A q * Complex.exp (s * (complexQuotientLogDet q : ℂ)) ∂D.measure := by
    funext s
    exact integral_congr_ae (Filter.Eventually.of_forall (hEq s))
  rw [hFun]
  exact differentiableOn_integral_mul_cexp continuous_complexQuotientLogDet.measurable hS
    (fun s hs => (hInt s hs).congr (Filter.Eventually.of_forall (hEq s)))

/-- The corank-one dual integral is holomorphic on its open domain of absolute convergence. -/
theorem differentiableOn_complexUnequalDualIntegral_adjacent
    (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W : G → ℂ) (V : H → ℂ)
    {S : Set ℂ} (hS : IsOpen S) (hInt : ∀ s ∈ S, Integrable
      (complexUnequalDualKernel h W V s) (complexUnequalDualMeasure (r := r + 1) a D)) :
    DifferentiableOn ℂ (complexUnequalDualIntegral h a D W V) S := by
  rw [funext (complexUnequalDualIntegral_adjacent a D W V)]
  exact differentiableOn_complexUnequalIntegral_of_integrable h D (Wd W) (Vd V) hS
    (fun s hs => (integrable_complexUnequalDualKernel_adjacent_iff a D W V s).mp (hInt s hs))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
