import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Global.RankinSelberg.RealPlaceWhittakerAnalyticProof

/-! # The real-place functional equation from local equations on a uniform coefficient space -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator CategoryTheory.MonObj
open Langlands.LocalFactor.Archimedean Langlands.Global.HeckeFunctionalEquation
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

local instance uniformBridgeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance uniformBridgeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance (r : ℕ) : MeasurableSpace (Langlands.GeneralLinear (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Langlands.GeneralLinear (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (r + 1) ℝ) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := borel _
local instance (r : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient r ℝ) := ⟨rfl⟩

/-- Unequal-rank analytic equations on the specified local coefficient space.
All analytic and continuous-model normalization work remains in this premise. -/
def RealLocalUniformUnequalJacquetStatement : Prop := by
  classical
  exact
  ∀ (r t : ℕ) (h : t < r) (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
    RealJacquet.UnequalEquation h a D W W' ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock) (-a)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) *
        (RealJacquet.determinant es (-1) : ℂ))

/-- Positive equal-rank analytic equations on the local coefficient space. -/
def RealLocalUniformPositiveEqualJacquetStatement : Prop := by
  classical
  exact
  ∀ (r : ℕ), 0 < r → ∀ (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
    RealJacquet.EqualEquation a (-a) D W W' Φ ds es
      (ds.map RealLocalJacquet.dualBlock) (es.map RealLocalJacquet.dualBlock)
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)

/-- Actual global restrictions belong to the specified local coefficient space.
This is proved below using the actual common-vector growth bound. -/
def RealPlaceUniformWhittakerModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ ds : List RealBlock, T.realization.HasRealPlaceParameter v ds →
  ∀ W : Langlands.GeneralLinear (r + 1) ℝ → ℂ,
    (IsRealPlaceWhittaker F T ψ.complex v W → W ∈ realUniformWhittakerModel r ds a) ∧
    (IsRealPlaceWhittaker F T ψ.complex⁻¹ v W → W ∈ realUniformWhittakerModel r ds (-a))

section Membership

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The restriction map of an actual real-place map has a common exponent before source
vectors, because all its images lie in one cuspidal realization. -/
theorem exists_restriction_isRealUniformWhittakerIntertwiner
    (χ : AddChar (Adeles F) ℂ) (hχstd : IsStandardAdditiveCharacter F χ)
    (w : {v : InfinitePlace F // v.IsReal}) (c : ℝˣ)
    (hχ : ∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((realScaledCharacter c
          (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ))
    {r : ℕ} (T : Automorphic.CuspidalOperatorRealization F r)
    (b : FiniteAdelicGL F (r + 1)) {d : List RealBlock}
    {A : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space}
    (hA : T.realization.IsRealPlaceMap w d A) :
    ∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
        (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
      IsRealUniformWhittakerIntertwiner r d c B ∧
        ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  obtain ⟨B, hB, he⟩ := exists_restriction_isRealWhittakerIntertwiner
    realPlaceWhittakerAnalytic χ hχstd w c hχ T b hA
  obtain ⟨N, hN⟩ := RealPlaceRestriction.exists_uniform_norm_cuspWhittaker_realPlace_le T w b
  refine ⟨B, ⟨hB, N, fun f => ?_⟩, he⟩
  obtain ⟨C, hC0, hC⟩ := hN χ hχstd (A f)
  exact ⟨C, hC0, by simpa only [he f] using hC⟩

theorem restriction_mem_realUniformWhittakerModel {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (b : FiniteAdelicGL F (r + 1)) (d : List RealBlock) (a : ℝˣ)
    (hB : ∀ A : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space,
      T.realization.IsRealPlaceMap w d A →
      ∃ B : Automorphic.realStandardKFinite (r + 1) d →ₗ[ℂ]
          (Langlands.GeneralLinear (r + 1) ℝ → ℂ),
        IsRealUniformWhittakerIntertwiner r d a B ∧
          ∀ f, B f = fun g => cuspWhittaker F T χ (A f)
            (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))
    {x : T.Space} (hx : x ∈ T.realization.realPlaceIsotypic w d) :
    (fun g => cuspWhittaker F T χ x
      (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∈
        realUniformWhittakerModel r d a := by
  induction hx using Submodule.iSup_induction' with
  | mem A y hy =>
    obtain ⟨f, rfl⟩ := hy
    obtain ⟨B, hBi, hBf⟩ := hB A.1 A.2
    rw [← hBf f]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hBi ⟨f, rfl⟩)
  | zero =>
    have h0 : (fun g => cuspWhittaker F T χ (0 : T.Space)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) = 0 := by
      funext g
      have h := UnramifiedWhittaker.cuspWhittaker_smul F χ T 0 (0 : T.Space)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)
      rw [zero_smul, zero_mul] at h
      exact h
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have hadd : (fun g => cuspWhittaker F T χ (y + z)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
        (fun g => cuspWhittaker F T χ y
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) +
        (fun g => cuspWhittaker F T χ z
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
      funext g
      exact UnramifiedWhittaker.cuspWhittaker_add F χ hχ T y z _
    rw [hadd]
    exact Submodule.add_mem _ hy hz

end Membership

/-- Actual global restrictions belong to the refined uniform coefficient space. -/
theorem realPlaceUniformWhittakerModel : RealPlaceUniformWhittakerModelStatement.{u} := by
  intro F _ _ _ ψ hψ r T v a ha ds hds W
  have hstd : IsStandardAdditiveCharacter F ψ.complex :=
    isStandardAdditiveCharacter_of_unitary ψ hψ
  have hstd' : IsStandardAdditiveCharacter F ψ.complex⁻¹ :=
    Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hstd
  have hall : ∀ x : T.Space, x ∈ T.realization.realPlaceIsotypic v ds :=
    Submodule.eq_top_iff'.mp (T.realization.realPlaceIsotypic_eq_top T.irreducible hds)
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_realUniformWhittakerModel T ψ.complex hstd v b ds a
      (fun A hA => exists_restriction_isRealUniformWhittakerIntertwiner ψ.complex hstd v a
        (realComponent_complex ψ v a ha) T b hA) (hall x)
  · obtain ⟨x, b, rfl⟩ := hW
    exact restriction_mem_realUniformWhittakerModel T ψ.complex⁻¹ hstd' v b ds (-a)
      (fun A hA => exists_restriction_isRealUniformWhittakerIntertwiner ψ.complex⁻¹ hstd' v (-a)
        (realComponent_complex_inv ψ v a ha) T b hA) (hall x)

/-- The refined local equations and actual dual denominator comparison imply the exact
full real-place functional equation. -/
def RealPlaceUniformLocalTheoryReductionStatement : Prop :=
  RealLocalUniformUnequalJacquetStatement → RealLocalUniformPositiveEqualJacquetStatement →
    RealPlaceContragredientPairLStatement.{u} → RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceUniformLocalTheoryReduction : RealPlaceUniformLocalTheoryReductionStatement.{u} := by
  intro hU hE hD
  have hB := realPlaceUniformWhittakerModel.{u}
  apply realPlacePositiveAnalyticReduction
  constructor
  · intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a ha
      ds es dds ees hds hes hdds hees D W W' hW hW'
    have hWm := (hB F ψ hψ r T v a ha ds hds W).1 hW
    have hWm' := (hB F ψ hψ t T' v a ha es hes W').2 hW'
    have hEq := hU r t h ds es hds.1 hes.1 a D W W' hWm hWm'
    have hDen := hD F r t T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
    have hc := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
    have hc' := RealLocalJacquet.realMinusOneScalar_eq_parameter T' v es hes
    simpa only [RealJacquet.UnequalEquation, ← hDen, ← hc, ← hc'] using hEq
  · intro F _ _ _ ψ hψ r hr T Td T' Td' hTd hTd' v a ha
      ds es dds ees hds hes hdds hees D W W' Φ hW hW'
    have hWm := (hB F ψ hψ r T v a ha ds hds W).1 hW
    have hWm' := (hB F ψ hψ r T' v a ha es hes W').2 hW'
    have hEq := hE r hr ds es hds.1 hes.1 a D W W' Φ hWm hWm'
    have hDen := hD F r r T Td T' Td' hTd hTd' v ds es dds ees hds hes hdds hees
    have hc := RealLocalJacquet.realMinusOneScalar_eq_parameter T v ds hds
    simpa only [RealJacquet.EqualEquation, ← hDen, ← hc] using hEq

end Langlands.Global.RankinSelbergGlobal
