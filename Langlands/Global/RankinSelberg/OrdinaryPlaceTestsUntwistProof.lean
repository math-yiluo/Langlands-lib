import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsSplitCentre
import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Automorphic.RealPlaceParameterNormPowerTwist
import Langlands.Automorphic.ComplexPlaceParameterHeckeTwist
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.RealPlaceDeterminantGrowth
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.UnfoldingGL

/-! # Untwisting the ordinary archimedean tests from realizations trivial on the split centre

Proof of `OrdinaryPlaceTestsUntwistStatement`. Every actual cuspidal realization becomes
trivial on the split centre after a twist by `‖·‖^(-λ) ∘ det`. The twist shifts the local
parameters, multiplies the archimedean restrictions of global Whittaker functions by
`|det|^(-λ)` and a nonzero constant, and shifts the spectral variable of the ordinary integrals.
See the paired Markdown.
-/

noncomputable section
open NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor Langlands.LocalFactor.Archimedean ArchimedeanLocal
open Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.CuspidalPairPoles (IsTrivialOnSplitCentre)

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

/-! ## Shifting the spectral variable -/

namespace ArchimedeanLocal

section Shift

variable {K : Type*} [Field K]

/-- `|det g|^(s + t) = |det g|^s |det g|^t`. -/
theorem detPower_add (nabs : K → ℝ) {n : ℕ} (g : Langlands.GeneralLinear n K) (s t : ℂ) :
    detPower nabs g (s + t) = detPower nabs g s * detPower nabs g t := by
  rw [detPower, detPower, detPower, add_mul, Complex.exp_add]

/-- `|det diag(g, 1)|^s = |det g|^s`. -/
theorem detPower_padGL (nabs : K → ℝ) {m n : ℕ} (h : m ≤ n) (g : Langlands.GeneralLinear m K)
    (s : ℂ) : detPower nabs (padGL h g) s = detPower nabs g s := by
  rw [detPower, detPower, UnequalAnalytic.det_padGL]

variable [TopologicalSpace K] {t : ℕ}
  [MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient t K)]

omit [TopologicalSpace K] in
/-- Multiplying the two functions by `c |det|^a` and `c' |det|^b` multiplies the unequal-rank
integral by `c c'` and shifts its variable by `a + b`. -/
theorem unequalIntegral_detPower_mul (nabs : K → ℝ)
    (m : MeasureTheory.Measure (Langlands.RankinSelberg.LeftUnipotentQuotient t K)) {r : ℕ}
    (h : t < r) (W : Langlands.GeneralLinear (r + 1) K → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) K → ℂ) (a b c c' s : ℂ) :
    unequalIntegral nabs m h (fun g => c * detPower nabs g a * W g)
        (fun g => c' * detPower nabs g b * W' g) s =
      c * c' * unequalIntegral nabs m h W W' (s + (a + b)) := by
  unfold unequalIntegral
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext q
  simp only [unequalIntegrand, detPower_padGL]
  rw [show s + (a + b) - ((r - t : ℕ) : ℂ) / 2 = a + (b + (s - ((r - t : ℕ) : ℂ) / 2)) by ring,
    detPower_add, detPower_add]
  ring

/-- Multiplying the two functions by `c |det|^a` and `c' |det|^b` multiplies the equal-rank
integral by `c c'` and shifts its variable by `a + b`. -/
theorem equalIntegral_detPower_mul (nabs : K → ℝ)
    (m : MeasureTheory.Measure (Langlands.RankinSelberg.LeftUnipotentQuotient t K))
    (W W' : Langlands.GeneralLinear (t + 1) K → ℂ) (Φ : (Fin (t + 1) → K) → ℂ)
    (a b c c' s : ℂ) :
    equalIntegral nabs m (fun g => c * detPower nabs g a * W g)
        (fun g => c' * detPower nabs g b * W' g) Φ s =
      c * c' * equalIntegral nabs m W W' Φ (s + (a + b)) := by
  unfold equalIntegral
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext q
  simp only [equalIntegrand]
  rw [show s + (a + b) = a + (b + s) by ring, detPower_add, detPower_add]
  ring

end Shift

end ArchimedeanLocal

/-- Nonvanishing at points arbitrarily far to the right passes from `f` to `g` when
`f(s) = c g(s + a)`. -/
theorem exists_re_gt_ne_zero_of_eq_mul_shift {f g : ℂ → ℂ} {c a : ℂ}
    (hfg : ∀ s, f s = c * g (s + a)) (hf : ∀ σ : ℝ, ∃ s : ℂ, σ < s.re ∧ f s ≠ 0) (σ : ℝ) :
    ∃ s : ℂ, σ < s.re ∧ g s ≠ 0 := by
  obtain ⟨s, hs, hne⟩ := hf (σ - a.re)
  refine ⟨s + a, by rw [Complex.add_re]; linarith, fun h0 => hne ?_⟩
  rw [hfg, h0, mul_zero]

/-! ## Global Whittaker functions of a twist -/

section Whittaker

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}

local instance untwistRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance untwistContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance untwistFiniteGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance untwistFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance untwistStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance untwistSpaceGroup (T : CuspidalOperatorRealization F r) : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- The global Whittaker function of the twist of a vector by `ν ∘ det` is the original one
times `ν(det g)`. -/
theorem cuspWhittaker_heckeDeterminantTwist (T : CuspidalOperatorRealization F r)
    (ν : HeckeCharacter F) (χ : AddChar (Adeles F) ℂ) (x : T.Space) (p : Points F (r + 1)) :
    cuspWhittaker F (T.heckeDeterminantTwist ν) χ (T.realization.heckeDeterminantTwistEquiv ν x) p =
      (ν.adelicDeterminant (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) p) : ℂ) *
        cuspWhittaker F T χ x p := by
  have hf (z : Points F (r + 1)) :
      cuspFunction F (T.heckeDeterminantTwist ν) (T.realization.heckeDeterminantTwistEquiv ν x) z =
        (ν.adelicDeterminant (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z) : ℂ) *
          cuspFunction F T x z :=
    (RealPlaceWhittaker.cuspFunction_eq_evaluate F _ _ z).trans
      ((T.realization.evaluate_heckeDeterminantTwistEquiv ν x _).trans
        (congrArg (_ * ·) (RealPlaceWhittaker.cuspFunction_eq_evaluate F T x z).symm))
  have hu (y : unipotentAdelic F (r + 1)) :
      ν.adelicDeterminant (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) (y.val * p)) =
        ν.adelicDeterminant (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) p) := by
    have hdet : AdelicGL.determinant F (r + 1)
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) y.val) = 1 := by
      apply Units.ext
      exact (Unfolding.isUnitriangular_of_mem_unipotentAdelic F y).det_eq_one
    have hν : ν.adelicDeterminant (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) y.val) =
        1 := by
      change ν.onIdeles (AdelicGL.determinant F (r + 1) _) = 1
      rw [hdet, map_one]
    rw [map_mul, map_mul, hν, one_mul]
  simp only [cuspWhittaker, generalLinearWhittakerFunction, subgroupCharacterCoefficient]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change cuspFunction F (T.heckeDeterminantTwist ν) _ _ * _ =
    _ * (cuspFunction F T x _ * _)
  rw [hf, hu (Quotient.out y)]
  ring

omit [CompactSpace (AdeleQuotient F)] in
/-- The value of `‖·‖^s ∘ det` at an adelic point is `exp (s log ‖det p‖)`. -/
theorem normPower_adelicDeterminant_adelicEquiv (n : ℕ) (s : ℂ) (p : Points F n) :
    ((HeckeCharacter.normPower F s).adelicDeterminant n
        (GeneralLinearGroupPoints.adelicEquiv F n p) : ℂ) =
      Complex.exp (s * (Real.log (detNorm F n p) : ℂ)) :=
  RealPlaceNormPowerTwist.normPower_adelicDeterminant n s _

/-- An actual restriction at a real place of a global Whittaker function of the twist by
`‖·‖^(-λ) ∘ det` is a nonzero constant times `|det|^(-λ)` times an actual restriction of the
original realization. -/
theorem isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower
    (T : CuspidalOperatorRealization F r) (l : ℂ) (χ : AddChar (Adeles F) ℂ)
    (v : {v : InfinitePlace F // v.IsReal}) {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l))) χ v
      W) :
    ∃ (W₀ : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (c : ℂ), IsRealPlaceWhittaker F T χ v W₀ ∧
      c ≠ 0 ∧ W = fun g => c * ArchimedeanLocal.detPower realNormalizedAbs g (-l) * W₀ g := by
  obtain ⟨y, a, rfl⟩ := hW
  obtain ⟨x, rfl⟩ :=
    (T.realization.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F (-l))).surjective y
  refine ⟨_, Complex.exp (-l * (Real.log (detNorm F (r + 1) (finitePoint F (r + 1) a)) : ℂ)),
    ⟨x, a, rfl⟩, Complex.exp_ne_zero _, ?_⟩
  funext g
  rw [cuspWhittaker_heckeDeterminantTwist, normPower_adelicDeterminant_adelicEquiv,
    Unfolding.detNorm_mul, RealPlaceRestriction.detNorm_realPlacePoint,
    Real.log_mul (Langlands.Archimedean.RealLinkedJacquetStages.abs_det_pos g).ne'
      (Unfolding.detNorm_pos F (r + 1) _).ne', Complex.ofReal_add, mul_add, Complex.exp_add,
    ArchimedeanLocal.detPower, realNormalizedAbs]
  ring

/-- An actual restriction at a complex place of a global Whittaker function of the twist by
`‖·‖^(-λ) ∘ det` is a nonzero constant times `|det|_ℂ^(-λ)` times an actual restriction of the
original realization. -/
theorem isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower
    (T : CuspidalOperatorRealization F r) (l : ℂ) (χ : AddChar (Adeles F) ℂ)
    (w : {w : InfinitePlace F // w.IsComplex}) {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    (hW : IsComplexPlaceWhittaker F (T.heckeDeterminantTwist (HeckeCharacter.normPower F (-l)))
      χ w W) :
    ∃ (W₀ : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (c : ℂ), IsComplexPlaceWhittaker F T χ w W₀ ∧
      c ≠ 0 ∧ W = fun g => c * ArchimedeanLocal.detPower complexNormalizedAbs g (-l) * W₀ g := by
  obtain ⟨y, a, rfl⟩ := hW
  obtain ⟨x, rfl⟩ :=
    (T.realization.heckeDeterminantTwistEquiv (HeckeCharacter.normPower F (-l))).surjective y
  refine ⟨_, Complex.exp (-l * (Real.log (detNorm F (r + 1) (finitePoint F (r + 1) a)) : ℂ)),
    ⟨x, a, rfl⟩, Complex.exp_ne_zero _, ?_⟩
  funext g
  have hdet : ((g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  rw [cuspWhittaker_heckeDeterminantTwist, normPower_adelicDeterminant_adelicEquiv,
    Unfolding.detNorm_mul, ComplexPlaceAnalytic.detNorm_complexPlacePoint,
    Real.log_mul (pow_pos (norm_pos_iff.mpr hdet) 2).ne'
      (Unfolding.detNorm_pos F (r + 1) _).ne', Complex.ofReal_add, mul_add, Complex.exp_add,
    ArchimedeanLocal.detPower, complexNormalizedAbs]
  ring

end Whittaker

/-! ## The four implications -/

/-- Untwisting at a real place in unequal ranks. -/
theorem realUnequalOrdinaryPlaceTests_of_splitCentre
    (hS : RealUnequalOrdinaryPlaceTestsSplitCentreStatement.{u}) :
    RealUnequalOrdinaryPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T T' v a ha d d' hd hd'
  obtain ⟨l, hl⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T
  obtain ⟨l', hl'⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T'
  obtain ⟨W, W', D, hW, hW', hne⟩ := hS F ψ hψ r t h _ _ hl hl' v a ha _ _
    (T.hasRealPlaceParameter_heckeDeterminantTwist_normPower hd (-l))
    (T'.hasRealPlaceParameter_heckeDeterminantTwist_normPower hd' (-l'))
  obtain ⟨W₀, c, hW₀, -, rfl⟩ := isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower T l _ v hW
  obtain ⟨W₀', c', hW₀', -, rfl⟩ :=
    isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower T' l' _ v hW'
  exact ⟨W₀, W₀', D, hW₀, hW₀', exists_re_gt_ne_zero_of_eq_mul_shift
    (f := fun s => realUnequalIntegral h D
      (fun g => c * ArchimedeanLocal.detPower realNormalizedAbs g (-l) * W₀ g)
      (fun g => c' * ArchimedeanLocal.detPower realNormalizedAbs g (-l') * W₀' g) s)
    (g := fun s => realUnequalIntegral h D W₀ W₀' s)
    (fun s => ArchimedeanLocal.unequalIntegral_detPower_mul realNormalizedAbs D.measure h W₀ W₀'
      (-l) (-l') c c' s) hne⟩

/-- Untwisting at a complex place in unequal ranks. -/
theorem complexUnequalOrdinaryPlaceTests_of_splitCentre
    (hS : ComplexUnequalOrdinaryPlaceTestsSplitCentreStatement.{u}) :
    ComplexUnequalOrdinaryPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T T' w a ha d d' hd hd'
  obtain ⟨l, hl⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T
  obtain ⟨l', hl'⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T'
  obtain ⟨e, he⟩ := ComplexPlaceHeckeTwist.exists_hasComplexPlaceParameter
    (HeckeCharacter.normPower F (-l)) w
  obtain ⟨e', he'⟩ := ComplexPlaceHeckeTwist.exists_hasComplexPlaceParameter
    (HeckeCharacter.normPower F (-l')) w
  obtain ⟨W, W', D, hW, hW', hne⟩ := hS F ψ hψ r t h _ _ hl hl' w a ha _ _
    (OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul hd he)
    (OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul hd' he')
  obtain ⟨W₀, c, hW₀, -, rfl⟩ :=
    isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower T l _ w hW
  obtain ⟨W₀', c', hW₀', -, rfl⟩ :=
    isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower T' l' _ w hW'
  exact ⟨W₀, W₀', D, hW₀, hW₀', exists_re_gt_ne_zero_of_eq_mul_shift
    (f := fun s => complexUnequalIntegral h D
      (fun g => c * ArchimedeanLocal.detPower complexNormalizedAbs g (-l) * W₀ g)
      (fun g => c' * ArchimedeanLocal.detPower complexNormalizedAbs g (-l') * W₀' g) s)
    (g := fun s => complexUnequalIntegral h D W₀ W₀' s)
    (fun s => ArchimedeanLocal.unequalIntegral_detPower_mul complexNormalizedAbs D.measure h W₀
      W₀' (-l) (-l') c c' s) hne⟩

/-- Untwisting at a real place in equal positive ranks. -/
theorem realEqualOrdinaryPlaceTests_of_splitCentre
    (hS : RealEqualOrdinaryPlaceTestsSplitCentreStatement.{u}) :
    RealEqualOrdinaryPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T T' v a ha d d' hd hd'
  obtain ⟨l, hl⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T
  obtain ⟨l', hl'⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T'
  obtain ⟨W, W', Φ, D, hW, hW', hne⟩ := hS F ψ hψ r hr _ _ hl hl' v a ha _ _
    (T.hasRealPlaceParameter_heckeDeterminantTwist_normPower hd (-l))
    (T'.hasRealPlaceParameter_heckeDeterminantTwist_normPower hd' (-l'))
  obtain ⟨W₀, c, hW₀, -, rfl⟩ := isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower T l _ v hW
  obtain ⟨W₀', c', hW₀', -, rfl⟩ :=
    isRealPlaceWhittaker_of_heckeDeterminantTwist_normPower T' l' _ v hW'
  exact ⟨W₀, W₀', Φ, D, hW₀, hW₀', exists_re_gt_ne_zero_of_eq_mul_shift
    (f := fun s => realEqualIntegral D
      (fun g => c * ArchimedeanLocal.detPower realNormalizedAbs g (-l) * W₀ g)
      (fun g => c' * ArchimedeanLocal.detPower realNormalizedAbs g (-l') * W₀' g) Φ s)
    (g := fun s => realEqualIntegral D W₀ W₀' Φ s)
    (fun s => ArchimedeanLocal.equalIntegral_detPower_mul realNormalizedAbs D.measure W₀ W₀' Φ
      (-l) (-l') c c' s) hne⟩

/-- Untwisting at a complex place in equal positive ranks. -/
theorem complexEqualOrdinaryPlaceTests_of_splitCentre
    (hS : ComplexEqualOrdinaryPlaceTestsSplitCentreStatement.{u}) :
    ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} := by
  intro F _ _ _ ψ hψ r hr T T' w a ha d d' hd hd'
  obtain ⟨l, hl⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T
  obtain ⟨l', hl'⟩ := NormPowerTwist.exists_normPower_twist_isTrivialOnSplitCentre T'
  obtain ⟨e, he⟩ := ComplexPlaceHeckeTwist.exists_hasComplexPlaceParameter
    (HeckeCharacter.normPower F (-l)) w
  obtain ⟨e', he'⟩ := ComplexPlaceHeckeTwist.exists_hasComplexPlaceParameter
    (HeckeCharacter.normPower F (-l')) w
  obtain ⟨W, W', Φ, D, hW, hW', hne⟩ := hS F ψ hψ r hr _ _ hl hl' w a ha _ _
    (OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul hd he)
    (OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist_mul hd' he')
  obtain ⟨W₀, c, hW₀, -, rfl⟩ :=
    isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower T l _ w hW
  obtain ⟨W₀', c', hW₀', -, rfl⟩ :=
    isComplexPlaceWhittaker_of_heckeDeterminantTwist_normPower T' l' _ w hW'
  exact ⟨W₀, W₀', Φ, D, hW₀, hW₀', exists_re_gt_ne_zero_of_eq_mul_shift
    (f := fun s => complexEqualIntegral D
      (fun g => c * ArchimedeanLocal.detPower complexNormalizedAbs g (-l) * W₀ g)
      (fun g => c' * ArchimedeanLocal.detPower complexNormalizedAbs g (-l') * W₀' g) Φ s)
    (g := fun s => complexEqualIntegral D W₀ W₀' Φ s)
    (fun s => ArchimedeanLocal.equalIntegral_detPower_mul complexNormalizedAbs D.measure W₀ W₀' Φ
      (-l) (-l') c c' s) hne⟩

/-- **Untwisting premise.** Each ordinary nonvanishing statement for realizations trivial on
the split centre implies the same statement for all actual cuspidal realizations. -/
theorem ordinaryPlaceTestsUntwist : OrdinaryPlaceTestsUntwistStatement.{u} :=
  ⟨realUnequalOrdinaryPlaceTests_of_splitCentre, complexUnequalOrdinaryPlaceTests_of_splitCentre,
    realEqualOrdinaryPlaceTests_of_splitCentre, complexEqualOrdinaryPlaceTests_of_splitCentre⟩

end Langlands.Global.RankinSelbergGlobal
