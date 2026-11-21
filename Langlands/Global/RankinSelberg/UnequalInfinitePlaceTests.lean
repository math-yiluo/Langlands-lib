import Langlands.Global.RankinSelberg.EqualInfinitePlaceTests
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Unequal-rank test integrals at individual infinite places -/

noncomputable section
open NumberField Filter
open scoped Classical CategoryTheory.MonObj Topology
set_option autoImplicit false

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation
open ArchimedeanLocal

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

namespace HolomorphicNonzeroOnRightHalfPlane

end HolomorphicNonzeroOnRightHalfPlane

section AtPlace

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} (h : t < r) (T : CuspidalOperatorRealization F r)
  (T' : CuspidalOperatorRealization F t)
  (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))

/-- One actual pair of real-place restrictions for both block-zero and dual tests. -/
def HasRealUnequalPlaceTest (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ) : Prop :=
  ∃ (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (D : RealQuotientMeasureData t),
    IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
    HolomorphicNonzeroOnRightHalfPlane (realUnequalIntegral h D W W') ∧
    HolomorphicNonzeroOnRightHalfPlane (realUnequalDualIntegral h a D W W')

/-- One actual pair of complex-place restrictions for both block-zero and dual tests. -/
def HasComplexUnequalPlaceTest (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ) : Prop :=
  ∃ (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℂ → ℂ)
    (D : ComplexQuotientMeasureData t),
    IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
    HolomorphicNonzeroOnRightHalfPlane (complexUnequalIntegral h D W W') ∧
    HolomorphicNonzeroOnRightHalfPlane (complexUnequalDualIntegral h a D W W')

end AtPlace

/-- The real local test assertion under the data of the real unequal-rank local equation. -/
def RealUnequalPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    T.realization.HasRealPlaceParameter v d →
    T'.realization.HasRealPlaceParameter v d' →
    Td.realization.HasRealPlaceParameter v dd →
    Td'.realization.HasRealPlaceParameter v dd' →
    HasRealUnequalPlaceTest h T T' ψ v a

/-- The complex local test assertion under the data of the complex unequal-rank local equation. -/
def ComplexUnequalPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' dd dd' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d →
    T'.realization.HasComplexPlaceParameter w d' →
    Td.realization.HasComplexPlaceParameter w dd →
    Td'.realization.HasComplexPlaceParameter w dd' →
    HasComplexUnequalPlaceTest h T T' ψ w a

/-- The two independent local existence inputs for the unequal-rank archimedean product. -/
def UnequalInfinitePlaceTestsStatement : Prop :=
  RealUnequalPlaceTestsStatement.{u} ∧ ComplexUnequalPlaceTestsStatement.{u}

end Langlands.Global.RankinSelbergGlobal
