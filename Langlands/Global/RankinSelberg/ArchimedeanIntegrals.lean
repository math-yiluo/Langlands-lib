import Langlands.Global.RankinSelberg.UnequalIntegrals
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Group.GL.LowerBlockLocalizationCoordinates
import Langlands.LocalFactor.ArchimedeanScaling

/-! # Archimedean local Rankin–Selberg integrals

Jacquet 2009, formulas (2.4)–(2.6), p.6, over `ℝ` and `ℂ`: the unequal-rank integral
`Ψ(s; W, W')`, the block integral `Ψ_(n-m-1)(s; W, W')` with the rectangular matrix
variable of the Library's `rectangularPoint`, the equal-rank integral `Ψ(s; W, W', Φ)` with
the last row, the dual `W̃(g) = W(w_n ᵗg⁻¹)`, right translation by `w_(n,m)`, and the
Fourier transform with the positive sign of the Library's global `fourierTransform`.
The generic definitions take the normalized absolute value as a function `nabs`; the
complex one is the square of the usual one. Quotient measures on `N \ GL` are data. See
the paired Markdown.
-/

noncomputable section
universe uK
open MeasureTheory
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow rectangularMeasure)

section Generic

variable {K : Type uK} [Field K]

/-- `|det g|^s` for the absolute value `nabs`, as the complex exponential of
`s · log nabs(det g)` (the real logarithm). -/
def detPower (nabs : K → ℝ) {n : ℕ} (g : Langlands.GeneralLinear n K) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log (nabs (Matrix.det g.val)) : ℂ))

/-- The integrand `W(diag(g, 1_(n-m))) W'(g) |det g|^(s-(n-m)/2)` of `Ψ(s; W, W')`,
for `n = r + 1 > m = t + 1`, evaluated at a representative of the class `q ∈ N_m \ GL_m`. -/
def unequalIntegrand (nabs : K → ℝ) {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) K → ℂ) (W' : Langlands.GeneralLinear (t + 1) K → ℂ)
    (s : ℂ) (q : LeftUnipotentQuotient t K) : ℂ :=
  let g := q.out
  W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) * W' g *
    detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2)

/-- The block matrix `[[g, 0, 0], [x, 1_(n-m-1), 0], [0, 0, 1]]`, with the coordinates of
the Library's global `rectangularPoint`. -/
def rectangularPoint {r t : ℕ} (h : t < r) (g : Langlands.GeneralLinear (t + 1) K)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K) : Langlands.GeneralLinear (r + 1) K :=
  GeneralLinear.reindex
    (finCongr (congrArg (fun a : ℕ => a + 1) (Nat.add_sub_of_le (Nat.succ_le_of_lt h))))
    (GeneralLinear.lowerBlockLocalization 1 g x 1)

/-- The Weyl element `w_(n,m) = diag(1_m, w_(n-m))`, with the coordinates of the Library's
global `unfoldingWeyl`. -/
def unfoldingWeyl {r t : ℕ} (h : t < r) : Langlands.GeneralLinear (r + 1) K :=
  GeneralLinear.reindex
    (finCongr (Nat.add_sub_of_le (Nat.le_of_lt (Nat.succ_lt_succ h))))
    (GeneralLinear.blockSum (1, GeneralLinear.weylLong ((r + 1) - (t + 1)) K))

/-- The dual function `W̃(g) = W(w_n ᵗg⁻¹)`, with the `w_n` of `GeneralLinear.weylLong`
used by the Library's global `dualFunction`. -/
def dualFunction (n : ℕ) (W : Langlands.GeneralLinear n K → ℂ)
    (g : Langlands.GeneralLinear n K) : ℂ :=
  W (GeneralLinear.weylLong n K * GeneralLinear.inverseTranspose n K g)

/-- Right translation `ρ(a) W (g) = W(g a)`. -/
def translateFunction {n : ℕ} (a : Langlands.GeneralLinear n K)
    (W : Langlands.GeneralLinear n K → ℂ) : Langlands.GeneralLinear n K → ℂ :=
  fun g => W (g * a)

/-- The integrand `W([[g,0,0],[x,1,0],[0,0,1]]) W'(g) |det g|^(s-(n-m)/2)` of the block
integral `Ψ_(n-m-1)(s; W, W')` (Jacquet's (2.5) with `j = n - m - 1`). -/
def blockKernel (nabs : K → ℝ) {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) K → ℂ) (W' : Langlands.GeneralLinear (t + 1) K → ℂ)
    (s : ℂ) (q : LeftUnipotentQuotient t K)
    (x : Matrix (Fin (r - (t + 1))) (Fin (t + 1)) K) : ℂ :=
  let g := q.out
  W (rectangularPoint h g x) * W' g * detPower nabs g (s - ((r - t : ℕ) : ℂ) / 2)

/-- The integrand `W(g) W'(g) Φ(e_n g) |det g|^s` of `Ψ(s; W, W', Φ)`, with `e_n g` the
last row. -/
def equalIntegrand [TopologicalSpace K] (nabs : K → ℝ) {r : ℕ}
    (W W' : Langlands.GeneralLinear (r + 1) K → ℂ) (Φ : (Fin (r + 1) → K) → ℂ) (s : ℂ)
    (q : LeftUnipotentQuotient r K) : ℂ :=
  let g := q.out
  W g * W' g * Φ (lastRow g) * detPower nabs g s

variable [MeasurableSpace K]

/-- The Fourier transform `Φ̂(x) = ∫ Φ(y) χ(∑_j y_j x_j) dy` for the product measure of `ν`,
with the positive sign of the Library's global `fourierTransform`. -/
def fourierTransform (χ : AddChar K ℂ) (ν : Measure K) {n : ℕ} (Φ : (Fin n → K) → ℂ)
    (x : Fin n → K) : ℂ :=
  ∫ y, Φ y * χ (∑ j, y j * x j) ∂Measure.pi (fun _ : Fin n => ν)

variable [TopologicalSpace K] {t : ℕ} [MeasurableSpace (LeftUnipotentQuotient t K)]

/-- The unequal-rank integral `Ψ(s; W, W') = ∫_(N_m \ GL_m) W(diag(g, 1)) W'(g)
|det g|^(s-(n-m)/2) dg` for the quotient measure `μ`. -/
def unequalIntegral (nabs : K → ℝ) (μ : Measure (LeftUnipotentQuotient t K)) {r : ℕ}
    (h : t < r) (W : Langlands.GeneralLinear (r + 1) K → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) K → ℂ) (s : ℂ) : ℂ :=
  ∫ q, unequalIntegrand nabs h W W' s q ∂μ

/-- The block integral `Ψ_(n-m-1)(s; W, W')`: the rectangular variable, with the product
measure of `ν`, is integrated first. -/
def blockIntegral (nabs : K → ℝ) (μ : Measure (LeftUnipotentQuotient t K))
    (ν : AdditiveHaarMeasure K) {r : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) K → ℂ) (W' : Langlands.GeneralLinear (t + 1) K → ℂ)
    (s : ℂ) : ℂ :=
  ∫ q, ∫ x, blockKernel nabs h W W' s q x ∂rectangularMeasure ν (r - (t + 1)) (t + 1) ∂μ

/-- The equal-rank integral `Ψ(s; W, W', Φ)` for the quotient measure `μ`. -/
def equalIntegral (nabs : K → ℝ) (μ : Measure (LeftUnipotentQuotient t K))
    (W W' : Langlands.GeneralLinear (t + 1) K → ℂ) (Φ : (Fin (t + 1) → K) → ℂ) (s : ℂ) : ℂ :=
  ∫ q, equalIntegrand nabs W W' Φ s q ∂μ

end Generic

section MeasureData

variable (t : ℕ) (K : Type uK) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace (Langlands.GeneralLinear (t + 1) K)]
  [BorelSpace (Langlands.GeneralLinear (t + 1) K)]
  [MeasurableSpace (GeneralLinear.upperUnipotent (t + 1) K)]
  [BorelSpace (GeneralLinear.upperUnipotent (t + 1) K)]
  [MeasurableSpace (LeftUnipotentQuotient t K)] [BorelSpace (LeftUnipotentQuotient t K)]

/-- A quotient measure on `N_(t+1) \ GL_(t+1)` together with the Haar measures it is
compatible with: a Haar measure on `GL_(t+1)`, a right-invariant Haar measure on
`N_(t+1)`, and the Weil integration formula (`IsCompatible`). -/
structure QuotientMeasureData where
  /-- The Haar measure on `GL_(t+1)`. -/
  groupHaar : Measure (Langlands.GeneralLinear (t + 1) K)
  groupHaar_isHaar : groupHaar.IsHaarMeasure
  /-- The Haar measure on `N_(t+1)`. -/
  unipotentHaar : Measure (GeneralLinear.upperUnipotent (t + 1) K)
  unipotentHaar_isHaar : unipotentHaar.IsHaarMeasure
  unipotentHaar_rightInvariant : unipotentHaar.IsMulRightInvariant
  /-- The quotient measure. -/
  measure : Measure (LeftUnipotentQuotient t K)
  compatible : QuotientIntegration.IsCompatible (GeneralLinear.upperUnipotent (t + 1) K)
    groupHaar unipotentHaar measure

end MeasureData

section Places

local instance archimedeanComplexGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℂ) := borel _
local instance archimedeanComplexGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℂ) := ⟨rfl⟩
local instance archimedeanComplexNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℂ) := borel _
local instance archimedeanComplexNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℂ) := ⟨rfl⟩
local instance archimedeanComplexQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℂ) := borel _
local instance archimedeanComplexQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℂ) := ⟨rfl⟩
local instance archimedeanRealGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance archimedeanRealGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance archimedeanRealNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance archimedeanRealNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance archimedeanRealQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance archimedeanRealQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- The normalized absolute value of `ℂ`: the square `|z|²` of the usual one. -/
def complexNormalizedAbs (z : ℂ) : ℝ := ‖z‖ ^ 2

/-- The normalized absolute value of `ℝ`: the usual one. -/
def realNormalizedAbs (x : ℝ) : ℝ := |x|

/-- Quotient measure data on `N_(t+1)(ℂ) \ GL_(t+1)(ℂ)`, with Borel measurable structures. -/
abbrev ComplexQuotientMeasureData (t : ℕ) := QuotientMeasureData t ℂ

/-- Quotient measure data on `N_(t+1)(ℝ) \ GL_(t+1)(ℝ)`, with Borel measurable structures. -/
abbrev RealQuotientMeasureData (t : ℕ) := QuotientMeasureData t ℝ

/-- The additive measure on `ℂ` self-dual for `complexScaledCharacter a`:
`|a| · (twice Lebesgue measure)`. -/
def complexSelfDualMeasure (a : ℂˣ) : AdditiveHaarMeasure ℂ :=
  complexScaledMeasure ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero)

/-- The additive measure on `ℝ` self-dual for `realScaledCharacter a`:
`|a|^(1/2) · (Lebesgue measure)`. -/
def realSelfDualMeasure (a : ℝˣ) : AdditiveHaarMeasure ℝ :=
  realScaledMeasure (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))

/-! ### Complex places -/

/-- The integrand of `Ψ(s; W, W')` at a complex place. -/
def complexUnequalIntegrand {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) : LeftUnipotentQuotient t ℂ → ℂ :=
  unequalIntegrand complexNormalizedAbs h W W' s

/-- `Ψ(s; W, W')` at a complex place, for the quotient measure of `D`. -/
def complexUnequalIntegral {r t : ℕ} (h : t < r) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) : ℂ :=
  unequalIntegral complexNormalizedAbs D.measure h W W' s

/-- The integrand of the dual block integral `Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` at a complex
place, as a function on the product of the quotient and the rectangular matrix space. -/
def complexUnequalDualKernel {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) : LeftUnipotentQuotient t ℂ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ → ℂ :=
  fun p => blockKernel complexNormalizedAbs h
    (translateFunction (unfoldingWeyl h) (dualFunction (r + 1) W)) (dualFunction (t + 1) W')
    s p.1 p.2

/-- The product measure, quotient times rectangular, on which the dual block integral at a
complex place converges absolutely; the rectangular measure is self-dual for
`complexScaledCharacter a`. -/
def complexUnequalDualMeasure {r t : ℕ} (a : ℂˣ) (D : ComplexQuotientMeasureData t) :
    Measure (LeftUnipotentQuotient t ℂ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :=
  D.measure.prod (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1))

/-- The dual integral `Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` at a complex place, with the
rectangular measure self-dual for `complexScaledCharacter a`. -/
def complexUnequalDualIntegral {r t : ℕ} (h : t < r) (a : ℂˣ)
    (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (s : ℂ) : ℂ :=
  blockIntegral complexNormalizedAbs D.measure (complexSelfDualMeasure a) h
    (translateFunction (unfoldingWeyl h) (dualFunction (r + 1) W)) (dualFunction (t + 1) W') s

/-- The Fourier transform at a complex place, for `complexScaledCharacter a` and its
self-dual measure. -/
def complexFourierTransform (a : ℂˣ) {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) : (Fin n → ℂ) → ℂ :=
  fourierTransform (complexScaledCharacter a).complex (complexSelfDualMeasure a).measure Φ

/-- The integrand of `Ψ(s; W, W', Φ)` at a complex place. -/
def complexEqualIntegrand {r : ℕ} (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) : LeftUnipotentQuotient r ℂ → ℂ :=
  equalIntegrand complexNormalizedAbs W W' Φ s

/-- `Ψ(s; W, W', Φ)` at a complex place, for the quotient measure of `D`. -/
def complexEqualIntegral {r : ℕ} (D : ComplexQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) : ℂ :=
  equalIntegral complexNormalizedAbs D.measure W W' Φ s

/-- The dual integral `Ψ(s; W̃, W̃', Φ̂)` at a complex place, with the Fourier transform for
`complexScaledCharacter a` and its self-dual measure. -/
def complexEqualDualIntegral {r : ℕ} (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) : ℂ :=
  equalIntegral complexNormalizedAbs D.measure (dualFunction (r + 1) W)
    (dualFunction (r + 1) W') (complexFourierTransform a Φ) s

/-! ### Real places -/

/-- The integrand of `Ψ(s; W, W')` at a real place. -/
def realUnequalIntegrand {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) : LeftUnipotentQuotient t ℝ → ℂ :=
  unequalIntegrand realNormalizedAbs h W W' s

/-- `Ψ(s; W, W')` at a real place, for the quotient measure of `D`. -/
def realUnequalIntegral {r t : ℕ} (h : t < r) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) : ℂ :=
  unequalIntegral realNormalizedAbs D.measure h W W' s

/-- The integrand of the dual block integral `Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` at a real
place, as a function on the product of the quotient and the rectangular matrix space. -/
def realUnequalDualKernel {r t : ℕ} (h : t < r)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) : LeftUnipotentQuotient t ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ → ℂ :=
  fun p => blockKernel realNormalizedAbs h
    (translateFunction (unfoldingWeyl h) (dualFunction (r + 1) W)) (dualFunction (t + 1) W')
    s p.1 p.2

/-- The product measure, quotient times rectangular, on which the dual block integral at a
real place converges absolutely; the rectangular measure is self-dual for
`realScaledCharacter a`. -/
def realUnequalDualMeasure {r t : ℕ} (a : ℝˣ) (D : RealQuotientMeasureData t) :
    Measure (LeftUnipotentQuotient t ℝ × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ) :=
  D.measure.prod (rectangularMeasure (realSelfDualMeasure a) (r - (t + 1)) (t + 1))

/-- The dual integral `Ψ_(n-m-1)(s; ρ(w_(n,m)) W̃, W̃')` at a real place, with the
rectangular measure self-dual for `realScaledCharacter a`. -/
def realUnequalDualIntegral {r t : ℕ} (h : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (s : ℂ) : ℂ :=
  blockIntegral realNormalizedAbs D.measure (realSelfDualMeasure a) h
    (translateFunction (unfoldingWeyl h) (dualFunction (r + 1) W)) (dualFunction (t + 1) W') s

/-- The Fourier transform at a real place, for `realScaledCharacter a` and its self-dual
measure. -/
def realFourierTransform (a : ℝˣ) {n : ℕ} (Φ : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fourierTransform (realScaledCharacter a).complex (realSelfDualMeasure a).measure Φ

/-- The integrand of `Ψ(s; W, W', Φ)` at a real place. -/
def realEqualIntegrand {r : ℕ} (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) : LeftUnipotentQuotient r ℝ → ℂ :=
  equalIntegrand realNormalizedAbs W W' Φ s

/-- `Ψ(s; W, W', Φ)` at a real place, for the quotient measure of `D`. -/
def realEqualIntegral {r : ℕ} (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) : ℂ :=
  equalIntegral realNormalizedAbs D.measure W W' Φ s

/-- The dual integral `Ψ(s; W̃, W̃', Φ̂)` at a real place, with the Fourier transform for
`realScaledCharacter a` and its self-dual measure. -/
def realEqualDualIntegral {r : ℕ} (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Φ : (Fin (r + 1) → ℝ) → ℂ) (s : ℂ) : ℂ :=
  equalIntegral realNormalizedAbs D.measure (dualFunction (r + 1) W)
    (dualFunction (r + 1) W') (realFourierTransform a Φ) s

end Places

end Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
