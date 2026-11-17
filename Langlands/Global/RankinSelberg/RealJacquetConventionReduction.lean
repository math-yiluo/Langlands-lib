import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Mathlib.Tactic

/-! # A conditional conversion from Jacquet's real-place conventions

The analytic equations, central-character comparison, and equal-rank reflection law
are retained as named premises. The epsilon change and scalar algebra are proved here.
-/

noncomputable section
universe u
open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

namespace RealJacquet

/-- Product of the determinant multipliers of a real block presentation. -/
def determinant (ds : List RealBlock) (a : ℝˣ) : ℂˣ :=
  (ds.map fun d => d.determinant a).prod

theorem realSign_neg (a : ℝˣ) : realSign (-a) = realSign (-1) * realSign a := by
  apply Units.ext
  simp [coe_realSign, abs_neg, neg_div]

theorem realToComplex_neg (a : ℝˣ) :
    realToComplex (-a) = realToComplex (-1) * realToComplex a := by
  apply Units.ext
  simp [realToComplex]

theorem block_determinant_neg (d : RealBlock) (a : ℝˣ) :
    d.determinant (-a) = d.determinant (-1) * d.determinant a := by
  cases d with
  | character d =>
    change d.character (-a) = d.character (-1) * d.character a
    rw [← map_mul]
    congr 1
    simp
  | induced d =>
    change realSign (-a) * d.character (realToComplex (-a)) =
      (realSign (-1) * d.character (realToComplex (-1))) *
        (realSign a * d.character (realToComplex a))
    rw [realSign_neg a, realToComplex_neg a, map_mul]
    ac_rfl

theorem block_epsilon_neg (d : RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (d.epsilon (-a) c hc s : ℂ) =
      (d.determinant (-1) : ℂ) * (d.epsilon a c hc s : ℂ) := by
  rw [d.coe_epsilon, d.coe_epsilon, block_determinant_neg]
  simp only [Units.val_mul, Units.val_neg, abs_neg]
  ring

/-- Changing the sign of the additive character multiplies epsilon by the
determinant at `-1`, with the same positive Haar scale. -/
theorem epsilon_neg (ds : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (realEpsilon ds (-a) c hc s : ℂ) =
      (determinant ds (-1) : ℂ) * (realEpsilon ds a c hc s : ℂ) := by
  induction ds with
  | nil => simp [realEpsilon, determinant]
  | cons d ds ih =>
    simp only [realEpsilon, determinant, List.map_cons, List.prod_cons, Units.val_mul]
      at ih ⊢
    rw [block_epsilon_neg, ih]
    ring

theorem pair_epsilon_neg (ds es : List RealBlock) (a : ℝˣ)
    (c : NNReal) (hc : 0 < c) (s : ℂ) :
    (realPairEpsilon ds es (-a) c hc s : ℂ) =
      (determinant (realPairBlocks ds es) (-1) : ℂ) *
        (realPairEpsilon ds es a c hc s : ℂ) :=
  epsilon_neg _ a c hc s

/-- The local self-dual measure is unchanged by negating the character parameter. -/
theorem selfDualMeasure_neg (a : ℝˣ) : realSelfDualMeasure (-a) = realSelfDualMeasure a := by
  unfold realSelfDualMeasure
  congr 1
  simp

/-- The transform with character parameter `-a` is the positive transform
evaluated at the reflected argument. No regularity hypothesis on the function is needed. -/
theorem fourier_neg (a : ℝˣ) {n : ℕ} (Φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    realFourierTransform (-a) Φ x = realFourierTransform a Φ (-x) := by
  unfold realFourierTransform
  rw [selfDualMeasure_neg]
  unfold fourierTransform
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  change ((realScaledCharacter (-a)).complex _ : ℂ) = (realScaledCharacter a).complex _
  have hx : (∑ j, y j * (-x) j) = -(∑ j, y j * x j) := by
    simp [Finset.sum_neg_distrib]
  rw [hx]
  simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    realScaledCharacter_apply, Units.val_neg, neg_mul, mul_neg]

theorem unequal_sign (c d : ℂ) (hc : c ^ 2 = 1) (hd : d ^ 2 = 1)
    (r t : ℕ) :
    (c ^ (t + 1) * d) * (c ^ (t + 1) * d ^ (r + 1)) = d ^ r := by
  have hc' : c ^ (t + 1) * c ^ (t + 1) = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, hc, one_pow]
  calc
    _ = (c ^ (t + 1) * c ^ (t + 1)) * (d ^ r * d ^ 2) := by
      rw [pow_succ]
      ring
    _ = d ^ r := by rw [hc', hd]; ring

theorem equal_sign (c d : ℂ) (hc : c ^ 2 = 1) (hd : d ^ 2 = 1)
    (r : ℕ) :
    (c * d) * (c ^ r * (c ^ (r + 1) * d ^ (r + 1))) = d ^ r := by
  have hc' : c ^ r * c ^ r = 1 := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm, pow_mul, hc, one_pow]
  calc
    _ = (c ^ r * c ^ r) * (c ^ 2 * d ^ 2) * d ^ r := by
      simp only [pow_succ]
      ring
    _ = d ^ r := by rw [hc', hc, hd]; ring

/-- A convergence, holomorphy, continuation, and multiplied-out functional-equation
package. The integral functions are supplied separately so that iterated integrals
and integrals of product kernels have the same interface. -/
def EquationPackage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (K : ℂ → X → ℂ) (Kd : ℂ → Y → ℂ)
    (Z Zd L Ld E : ℂ → ℂ) (sign : ℂ) : Prop :=
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (K s) μ) ∧
    (∀ s : ℂ, σ < s.re → Integrable (Kd s) ν) ∧
    DifferentiableOn ℂ Z {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ Zd {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → Z s = M s) ∧
    (∀ s : ℂ, σ < s.re → Zd s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      L s * Md (1 - s) = sign * E s * Ld (1 - s) * M s

theorem EquationPackage.change_factor
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd L Ld E E' : ℂ → ℂ} {sign sign' : ℂ}
    (h : EquationPackage μ ν K Kd Z Zd L Ld E sign)
    (hE : ∀ s, sign * E s = sign' * E' s) :
    EquationPackage μ ν K Kd Z Zd L Ld E' sign' := by
  obtain ⟨σ, M, Md, hK, hKd, hZ, hZd, hM, hMd, hZM, hZdMd, hFE⟩ := h
  refine ⟨σ, M, Md, hK, hKd, hZ, hZd, hM, hMd, hZM, hZdMd, ?_⟩
  filter_upwards [hFE] with s hs
  rwa [← hE s]

/-- Transfer a dual package through an involutive scalar. The two reflection
facts, integrability equivalence and equality of the integral functions, are explicit. -/
theorem EquationPackage.reflect_dual
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ}
    {Kn Kp : ℂ → Y → ℂ} {Z Zn Zp L Ld E : ℂ → ℂ} {sign k : ℂ}
    (hk : k ^ 2 = 1)
    (hK : ∀ s, Integrable (Kn s) ν ↔ Integrable (Kp s) ν)
    (hZ : ∀ s, Zn s = k * Zp s)
    (h : EquationPackage μ ν K Kn Z Zn L Ld E sign) :
    EquationPackage μ ν K Kp Z Zp L Ld E (k * sign) := by
  have hkk : k * k = 1 := by simpa [pow_two] using hk
  have hZ' : Zp = fun s => k * Zn s := by
    funext s
    rw [hZ, ← mul_assoc, hkk, one_mul]
  obtain ⟨σ, M, Md, hK0, hKn, hZ0, hZn, hM, hMd, hZM, hZnMd, hFE⟩ := h
  refine ⟨σ, M, fun s => k * Md s, hK0, fun s hs => (hK s).mp (hKn s hs),
    ?_, ?_, hM, ?_, hZM, ?_, ?_⟩
  · exact hZ0
  · rw [hZ']
    exact hZn.const_mul k
  · exact (MeromorphicOn.const k).mul hMd
  · intro s hs
    rw [hZ']
    exact congrArg (k * ·) (hZnMd s hs)
  · filter_upwards [hFE] with s hs
    calc
      L s * (k * Md (1 - s)) = k * (L s * Md (1 - s)) := by ring
      _ = k * (sign * E s * Ld (1 - s) * M s) := by rw [hs]
      _ = (k * sign) * E s * Ld (1 - s) * M s := by ring

theorem representation_scalar_sq {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] [Nontrivial V] (ρ : Representation ℂ G V) (z : G)
    (hz : z * z = 1) (c : ℂ) (h : ∀ x, ρ z x = c • x) : c ^ 2 = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hρ : ρ z (ρ z x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, hz, map_one]
    rfl
  have hxx : (c * c) • x = (1 : ℂ) • x := by
    calc
      (c * c) • x = c • (c • x) := mul_smul _ _ _
      _ = ρ z (ρ z x) := by rw [h, h]
      _ = (1 : ℂ) • x := by rw [hρ, one_smul]
  simpa [pow_two] using (smul_left_injective ℂ hx) hxx

end RealJacquet

/-- The defined real minus-one scalar is involutive, including its fallback value. -/
theorem realMinusOneScalar_sq {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r)
    (v : {v : InfinitePlace F // v.IsReal}) : realMinusOneScalar T v ^ 2 = 1 := by
  classical
  let : AddCommGroup (Automorphic.RationalInvariantFunctions F (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Automorphic.ContinuousRationalFunctions F (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup (Automorphic.StableAutomorphicFunctions F (r + 1)) :=
    Submodule.addCommGroup _
  let : AddCommGroup T.Space := Submodule.addCommGroup _
  by_cases h : ∃ c : ℂ, ∀ x : T.Space,
    T.realization.realPlaceCompactRepresentation v (-1) x = c • x
  · exact RealJacquet.representation_scalar_sq
      (T.realization.realPlaceCompactRepresentation v)
      (-1 : Matrix.unitaryGroup (Fin (r + 1)) ℝ) (by simp)
      (realMinusOneScalar T v) (realMinusOneScalar_spec T v h)
  · rw [realMinusOneScalar, dite_eq_right h]
    norm_num

local instance realJacquetGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realJacquetGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realJacquetNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realJacquetNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realJacquetQMeasurable (n : ℕ) :
    MeasurableSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realJacquetQBorel (n : ℕ) :
    BorelSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

namespace RealJacquet

/-- The unequal-rank package with an independently specified epsilon parameter `b`.
The rectangular measure and positive epsilon scale use `a`. -/
def UnequalEquation {r t : ℕ} (h : t < r) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (ds es dds ees : List RealBlock) (b : ℝˣ) (sign : ℂ) : Prop :=
  EquationPackage D.measure (realUnequalDualMeasure (r := r) a D)
    (realUnequalIntegrand h W W') (realUnequalDualKernel h W W')
    (realUnequalIntegral h D W W') (realUnequalDualIntegral h a D W W')
    (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

/-- The equal-rank package with Fourier and epsilon parameter `b`, retaining the
positive epsilon scale prescribed by `a`. -/
def EqualEquation {r : ℕ} (a b : ℝˣ) (D : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ) : Prop :=
  EquationPackage D.measure D.measure
    (realEqualIntegrand W W' Φ)
    (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.dualFunction (r + 1) W')
      (realFourierTransform b Φ))
    (realEqualIntegral D W W' Φ) (realEqualDualIntegral b D W W' Φ)
    (fun s => ((realPairLFactor ds es).denominator s)⁻¹)
    (fun s => ((realPairLFactor dds ees).denominator s)⁻¹)
    (fun s => (realPairEpsilon ds es b (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ)) sign

end RealJacquet

/-- Jacquet's negative-character conventions, for the actual global restrictions.
This premise retains the local analytic theorem and the global-to-local membership step. -/
def RealJacquetRestrictionEquationStatement : Prop :=
  (by
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
    RealJacquet.UnequalEquation h a D W W' d d' dd dd' (-a)
      (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v)) ∧
  (by
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
    RealJacquet.EqualEquation a (-a) D W W' Φ d d' dd dd'
      (realMinusOneScalar T v ^ r))

/-- Compatibility of the determinant of the tensor parameter with the actual
minus-one compact scalars. This includes both parameter and central-action comparisons. -/
def RealPairCentralCompatibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (v : {v : InfinitePlace F // v.IsReal}) (d d' : List RealBlock),
    Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
    Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
    (RealJacquet.determinant (realPairBlocks d d') (-1) : ℂ) =
      realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v ^ (r + 1)

/-- The equal-rank negative Fourier dual integral is the positive one times the
product of minus-one scalars. The integrability and integral reflection laws remain open. -/
def RealEqualDualReflectionStatement : Prop := by
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
  (∀ s : ℂ,
    Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.dualFunction (r + 1) W')
      (realFourierTransform (-a) Φ) s) D.measure ↔
    Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W) (ArchimedeanLocal.dualFunction (r + 1) W')
      (realFourierTransform a Φ) s) D.measure) ∧
  (∀ s : ℂ, realEqualDualIntegral (-a) D W W' Φ s =
    (realMinusOneScalar T v * realMinusOneScalar T' v) *
      realEqualDualIntegral a D W W' Φ s)

/-- Internal reduction: the analytic restriction equation, the determinant/central
comparison, and equal-rank reflection suffice for the published real-place target. -/
def RealPlaceJacquetConventionReductionStatement : Prop :=
  RealJacquetRestrictionEquationStatement.{u} →
    RealPairCentralCompatibilityStatement.{u} →
    RealEqualDualReflectionStatement.{u} → RealPlaceFunctionalEquationStatement.{u}

/-- The convention conversion, with all analytic/model and reflection premises retained. -/
theorem realPlaceJacquetConventionReduction :
    RealPlaceJacquetConventionReductionStatement.{u} := by
  intro hJ hC hR
  constructor
  · intro F _ _ _ ψ hψ r t h T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
    change RealJacquet.UnequalEquation h a D W W' d d' dd dd' a
      (realMinusOneScalar T' v ^ r)
    have hEq := hJ.1 F ψ hψ r t h T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' hW hW'
    apply RealJacquet.EquationPackage.change_factor hEq
    intro s
    rw [RealJacquet.pair_epsilon_neg, hC F r t T T' v d d' hd hd']
    calc
      _ = ((realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v) *
          (realMinusOneScalar T v ^ (t + 1) * realMinusOneScalar T' v ^ (r + 1))) *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) := by ring
      _ = _ := by rw [RealJacquet.unequal_sign _ _
        (realMinusOneScalar_sq T v) (realMinusOneScalar_sq T' v)]
  · intro F _ _ _ ψ hψ r T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    change RealJacquet.EqualEquation a a D W W' Φ d d' dd dd'
      (realMinusOneScalar T' v ^ r)
    have hEq := hJ.2 F ψ hψ r T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    obtain ⟨hK, hZ⟩ := hR F ψ hψ r T Td T' Td' hTd hTd' v a hA
      d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
    have hk : (realMinusOneScalar T v * realMinusOneScalar T' v) ^ 2 = 1 := by
      rw [mul_pow, realMinusOneScalar_sq T v, realMinusOneScalar_sq T' v, one_mul]
    have hEp := RealJacquet.EquationPackage.reflect_dual hk hK hZ hEq
    apply RealJacquet.EquationPackage.change_factor hEp
    intro s
    rw [RealJacquet.pair_epsilon_neg, hC F r r T T' v d d' hd hd']
    calc
      _ = ((realMinusOneScalar T v * realMinusOneScalar T' v) *
          (realMinusOneScalar T v ^ r *
            (realMinusOneScalar T v ^ (r + 1) * realMinusOneScalar T' v ^ (r + 1)))) *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) := by ring
      _ = _ := by rw [RealJacquet.equal_sign _ _
        (realMinusOneScalar_sq T v) (realMinusOneScalar_sq T' v)]

end Langlands.Global.RankinSelbergGlobal
