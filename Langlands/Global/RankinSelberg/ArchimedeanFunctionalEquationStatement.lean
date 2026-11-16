import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.RankinSelberg.UnequalSemilocalEquationStatement
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # The archimedean Rankin–Selberg functional equation at one place

Jacquet 2009, Theorem 2.1 and formulas (2.4)–(2.6), pp.6–7, and Cogdell 2004, Theorems 3.5–3.6,
pp.216–217, for the archimedean restrictions `g ↦ W_x(ι_v(g) a)` of the global Whittaker
functions of actual cuspidal realizations. A complex place and a real place are stated
separately, each in the unequal-rank case `t < r` and in the equal-rank case. Each statement
asserts absolute convergence and holomorphy on a right half-plane, meromorphic continuation,
and the local functional equation in multiplied-out form, with the Library's archimedean pair
factors and the central sign `ω'_v(-1)^r`. See the paired Markdown.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance archimedeanEquationComplexGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℂ) := borel _
local instance archimedeanEquationComplexGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℂ) := ⟨rfl⟩
local instance archimedeanEquationComplexNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℂ) := borel _
local instance archimedeanEquationComplexNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℂ) := ⟨rfl⟩
local instance archimedeanEquationComplexQMeasurable (n : ℕ) :
    MeasurableSpace (RankinSelberg.LeftUnipotentQuotient n ℂ) := borel _
local instance archimedeanEquationComplexQBorel (n : ℕ) :
    BorelSpace (RankinSelberg.LeftUnipotentQuotient n ℂ) := ⟨rfl⟩
local instance archimedeanEquationRealGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance archimedeanEquationRealGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance archimedeanEquationRealNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance archimedeanEquationRealNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance archimedeanEquationRealQMeasurable (n : ℕ) :
    MeasurableSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance archimedeanEquationRealQBorel (n : ℕ) :
    BorelSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-! ### Complex places -/

/-- **Jacquet 2009, Theorem 2.1 (i)–(iii), unequal ranks, at a complex place.**

Let `T`, `T'` be actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)`, `t < r`, with
contragredients `Td`, `Td'`, over a number field `F` with an additive character `ψ` trivial
on `F`. Let `w` be a complex place, `ψ_w = complexScaledCharacter a` the component of `ψ` at
`w`, and `d`, `d'`, `dd`, `dd'` the parameters of `T`, `T'`, `Td`, `Td'` at `w`. For every
quotient measure `D` on `N_(t+1)(ℂ) \ GL_(t+1)(ℂ)` and archimedean restrictions `W` of a
Whittaker function of `T` for `ψ` and `W'` of one of `T'` for `ψ⁻¹` at `w`, there are a real
`σ` and meromorphic functions `M`, `Md` on `ℂ` such that, for `σ < Re s`, the integrands of
`Ψ(s; W, W')` and of `Ψ_(r-t-1)(s; ρ(w_(n,m)) W̃, W̃')` are absolutely integrable, both
integrals are holomorphic and equal `M(s)` and `Md(s)`; and off a discrete set
`L_w(s) Md(1 - s) = ω'_w(-1)^r ε_w(s) L∨_w(1 - s) M(s)`. -/
def ComplexUnequalFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' dd dd' : List ComplexCharacterData),
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
    Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization w d' →
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization w dd →
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization w dd' →
  ∀ (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    IsComplexPlaceWhittaker F T ψ.complex w W →
    IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexUnequalIntegrand h W W' s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalDualKernel h W W' s) (complexUnequalDualMeasure (r := r) a D)) ∧
    DifferentiableOn ℂ (complexUnequalIntegral h D W W') {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (complexUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexUnequalIntegral h D W W' s = M s) ∧
    (∀ s : ℂ, σ < s.re → complexUnequalDualIntegral h a D W W' s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexMinusOneScalar T' w ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor dd dd').denominator (1 - s))⁻¹ * M s

/-- **Jacquet 2009, Theorem 2.1 (i)–(iii), equal ranks, at a complex place.**

In the setting of `ComplexUnequalFunctionalEquationStatement` with `T`, `T'` both of rank
`r + 1`, for every quotient measure `D` on `N_(r+1)(ℂ) \ GL_(r+1)(ℂ)`, archimedean
restrictions `W`, `W'` and Schwartz function `Φ` on `ℂ^(r+1)`, there are a real `σ` and
meromorphic `M`, `Md` such that for `σ < Re s` the integrands of `Ψ(s; W, W', Φ)` and of
`Ψ(s; W̃, W̃', Φ̂)` (Fourier transform for `ψ_w` and its self-dual measure) are absolutely
integrable, both integrals are holomorphic and equal `M(s)` and `Md(s)`; and off a discrete
set `L_w(s) Md(1 - s) = ω'_w(-1)^r ε_w(s) L∨_w(1 - s) M(s)`. -/
def ComplexEqualFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' dd dd' : List ComplexCharacterData),
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization w d →
    Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization w d' →
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization w dd →
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization w dd' →
  ∀ (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    IsComplexPlaceWhittaker F T ψ.complex w W →
    IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s)
        D.measure) ∧
    DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → complexEqualDualIntegral a D W W' Φ s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexMinusOneScalar T' w ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor dd dd').denominator (1 - s))⁻¹ * M s

/-- **Result 1 at the complex places**: the unequal-rank and the equal-rank archimedean
functional equations at a complex place. -/
def ComplexPlaceFunctionalEquationStatement : Prop :=
  ComplexUnequalFunctionalEquationStatement.{u} ∧ ComplexEqualFunctionalEquationStatement.{u}

/-! ### Real places -/

/-- **Jacquet 2009, Theorem 2.1 (i)–(iii), unequal ranks, at a real place.**

The analogue of `ComplexUnequalFunctionalEquationStatement` at a real place `v`, with
`ψ_v = realScaledCharacter a`, the real parameters of `T`, `T'`, `Td`, `Td'` at `v`, the
absolute value `|x|`, the rectangular measure self-dual for `ψ_v`, the real pair factors,
`ε_v` normalized by `a` and `|a|^(1/2)`, and the sign `ω'_v(-1)^r`. -/
def RealUnequalFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
    Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v dd →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v dd' →
  ∀ (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    IsRealPlaceWhittaker F T ψ.complex v W →
    IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (realUnequalDualKernel h W W' s) (realUnequalDualMeasure (r := r) a D)) ∧
    DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (realUnequalDualIntegral h a D W W') {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → realUnequalIntegral h D W W' s = M s) ∧
    (∀ s : ℂ, σ < s.re → realUnequalDualIntegral h a D W W' s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((realPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        realMinusOneScalar T' v ^ r *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
          ((realPairLFactor dd dd').denominator (1 - s))⁻¹ * M s

/-- **Jacquet 2009, Theorem 2.1 (i)–(iii), equal ranks, at a real place.**

The analogue of `ComplexEqualFunctionalEquationStatement` at a real place `v`, with
`ψ_v = realScaledCharacter a`, a Schwartz function `Φ` on `ℝ^(r+1)`, its Fourier transform
for `ψ_v` and the self-dual measure `|a|^(1/2) dx`, the real pair factors, `ε_v` normalized
by `a` and `|a|^(1/2)`, and the sign `ω'_v(-1)^r`. -/
def RealEqualFunctionalEquationStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
    Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v dd →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v dd' →
  ∀ (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    IsRealPlaceWhittaker F T ψ.complex v W →
    IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform a Φ) s)
        D.measure) ∧
    DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → realEqualIntegral D W W' Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → realEqualDualIntegral a D W W' Φ s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((realPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        realMinusOneScalar T' v ^ r *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
          ((realPairLFactor dd dd').denominator (1 - s))⁻¹ * M s

/-- **Result 1 at the real places**: the unequal-rank and the equal-rank archimedean
functional equations at a real place. -/
def RealPlaceFunctionalEquationStatement : Prop :=
  RealUnequalFunctionalEquationStatement.{u} ∧ RealEqualFunctionalEquationStatement.{u}

/-- **Result 1 at all infinite places**: the conjunction of the complex-place and the
real-place statements. -/
def ArchimedeanFunctionalEquationStatement : Prop :=
  ComplexPlaceFunctionalEquationStatement.{u} ∧ RealPlaceFunctionalEquationStatement.{u}

end Langlands.Global.RankinSelbergGlobal
