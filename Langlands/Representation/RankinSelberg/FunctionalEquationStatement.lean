import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Whittaker.DualTransform
import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! Actual dual test data and proposition definitions for JPSS Theorem 2.7(iii). -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section DualData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The standard character of the scaled additive character `x ↦ ψ(a*x)` is
the shared scaled matrix character. -/
theorem standardCharacter_scale (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n : ℕ) :
    standardCharacter (ψ.scale a) n = scaledStandardCharacter ψ a n := by
  ext u
  rfl

/-- For `ψ⁻¹ = ψ.scale (-1)`, the standard character is the inverse character. -/
@[simp] theorem standardCharacter_scale_neg_one (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n := by
  rw [standardCharacter_scale, scaledStandardCharacter_neg_one]

@[simp] theorem inverseStandardCharacter_scale_neg_one
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    inverseStandardCharacter (ψ.scale (-1)) n = standardCharacter ψ n := by
  change (standardCharacter (ψ.scale (-1)) n)⁻¹ = _
  rw [standardCharacter_scale_neg_one]
  exact inv_inv (standardCharacter ψ n)

/-- The first dual function has the actual inverse additive character. -/
def firstDualFunction (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : WhittakerFunctions ψ n) : WhittakerFunctions (ψ.scale (-1)) n :=
  ⟨dualFunction n f.val, by
    simpa only [WhittakerFunctions, standardCharacter_scale_neg_one] using
      dualFunction_mem ψ f.property⟩

/-- The second dual function has the inverse of the inverse additive character. -/
def secondDualFunction (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : InverseWhittakerFunctions ψ n) : InverseWhittakerFunctions (ψ.scale (-1)) n :=
  ⟨dualFunction n f.val, by
    simpa only [InverseWhittakerFunctions, inverseStandardCharacter_scale_neg_one] using
      dualFunction_inverse_mem ψ f.property⟩

@[simp] theorem firstDualFunction_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : WhittakerFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    (firstDualFunction ψ n f).val g =
      f.val (weylLong (n + 1) F * inverseTranspose (n + 1) F g) := rfl

@[simp] theorem secondDualFunction_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : InverseWhittakerFunctions ψ n) (g : Langlands.GeneralLinear (n + 1) F) :
    (secondDualFunction ψ n f).val g =
      f.val (weylLong (n + 1) F * inverseTranspose (n + 1) F g) := rfl

/-- Right translation preserves the actual Whittaker covariance condition. -/
def translateWhittaker (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : WhittakerFunctions ψ n) (a : Langlands.GeneralLinear (n + 1) F) :
    WhittakerFunctions ψ n :=
  ⟨fun g => f.val (g * a), by
    intro u g
    change f.val ((u.val * g) * a) = (standardCharacter ψ n u : ℂ) * f.val (g * a)
    rw [mul_assoc, f.property]⟩

omit [IsTopologicalRing F] in
@[simp] theorem translateWhittaker_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : WhittakerFunctions ψ n) (a g : Langlands.GeneralLinear (n + 1) F) :
    (translateWhittaker ψ n f a).val g = f.val (g * a) := rfl

/-- The actual block Weyl representative `diag(I_(n+1), w_(r-n))`.
The reindexing only identifies the two equal natural-number dimensions. -/
def blockWeylAt (n r : ℕ) (hnr : n < r) : Langlands.GeneralLinear (r + 1) F :=
  GeneralLinear.reindex
    (finCongr (show (n + 1) + (r - n) = r + 1 by omega))
    (blockSum ((1 : Langlands.GeneralLinear (n + 1) F), weylLong (r - n) F))

end DualData

section CentralAction

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Scalar action of the actual central matrix `-I` on a specified coefficient
image. No central character on a possibly reducible original carrier is assumed. -/
def HasModelMinusOneScalar
    {θ : upperUnipotent (n + 1) F →* ℂˣ}
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ σ) (ζ : ℂˣ) : Prop :=
  ∀ f : (coefficientModel σ ℓ).toSubmodule,
    ∀ g : Langlands.GeneralLinear (n + 1) F,
      f.val.val ((-1) * g) = (ζ : ℂ) * f.val.val g

omit [TopologicalSpace F] in
/-- A nonzero specified functional makes the model's minus-one scalar unique. -/
theorem HasModelMinusOneScalar.unique
    {θ : upperUnipotent (n + 1) F →* ℂˣ}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {ℓ : functionals (upperUnipotent (n + 1) F) θ σ} (hℓ : ℓ.val ≠ 0)
    {ζ η : ℂˣ} (hζ : HasModelMinusOneScalar σ ℓ ζ)
    (hη : HasModelMinusOneScalar σ ℓ η) : ζ = η := by
  have hex : ∃ v, ℓ.val v ≠ 0 := by
    by_contra! h
    apply hℓ
    ext v
    exact h v
  obtain ⟨v, hv⟩ := hex
  have hf : (modelMap σ ℓ v).val.val 1 ≠ 0 := by
    change ℓ.val (σ 1 v) ≠ 0
    simpa only [map_one, Module.End.one_apply] using hv
  apply Units.ext
  exact (mul_right_cancel₀ hf) ((hζ (modelMap σ ℓ v) 1).symm.trans
    (hη (modelMap σ ℓ v) 1))

end CentralAction

/-- The required nonzero Laurent monomial in the actual spectral variable. -/
def epsilonMonomial (q : ℕ) (c : ℂˣ) (m : ℤ) (s : ℂ) : ℂ :=
  (c : ℂ) * spectralPoint q s ^ m

/-- Under the actual positive-cardinality condition, this expression is nonzero. -/
theorem epsilonMonomial_ne_zero (q : ℕ) (hq : 0 < (q : ℝ))
    (c : ℂˣ) (m : ℤ) (s : ℂ) : epsilonMonomial q c m s ≠ 0 := by
  unfold epsilonMonomial
  rw [spectralPoint_eq_spectralParameter q hq]
  exact mul_ne_zero c.ne_zero (zpow_ne_zero _ (Units.ne_zero _))

/-- Normalized functional equation, interpreted through rational continuations
away from their poles. Multiplication by `P` is division by `L=1/P`.
The dual continuation is evaluated at `1-s`, with the sign exponent explicit. -/
def NormalizedFunctionalEquation (q : ℕ) (P Pdual : Polynomial ℂ)
    (ζ c : ℂˣ) (e : ℕ) (m : ℤ) (R Rdual : RationalFunctions) : Prop :=
  ∀ s : ℂ,
    R.denom.eval (spectralPoint q s) ≠ 0 →
    Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
    Pdual.eval (spectralPoint q (1 - s)) *
        Rdual.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) =
      (ζ : ℂ) ^ e * epsilonMonomial q c m s *
        (P.eval (spectralPoint q s) * R.eval (RingHom.id ℂ) (spectralPoint q s))

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The equal-rank integral of the actual two transformed coefficient functions.
Its character is `ψ⁻¹`; it has not been identified with a contragredient by definition. -/
def dualEqualRankModelIntegral (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) : ℂ → ℂ :=
  equalRankIntegral (ψ.scale (-1)) abv μ
    (firstDualFunction ψ n f.val) (secondDualFunction ψ n f'.val) Φ

/-- Rational values of the transformed coefficient-image family, with all
Schwartz--Bruhat tests. No continuation or generator existence is assumed. -/
def dualEqualRankRationalValues (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) :
    Set RationalFunctions :=
  {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
    ∃ f' : (coefficientModel σ ℓ').toSubmodule,
    ∃ Φ : SchwartzBruhat (Fin (n + 1) → F),
      HasRationalContinuation q (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R}

/-- Equal-rank FE existence, including actual Fourier tests and rational
continuations. The constants and generator polynomials precede every test vector. -/
def EqualRankFunctionalEquationConclusion
    [MeasurableSpace F] (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  ∃ (ζ c : ℂˣ) (m : ℤ) (P Pdual : Polynomial ℂ),
    HasModelMinusOneScalar σ ℓ' ζ ∧
    IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P ∧
    IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') Pdual ∧
    ∀ f : (coefficientModel π ℓ).toSubmodule,
    ∀ f' : (coefficientModel σ ℓ').toSubmodule,
    ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
      ∃ (Φhat : SchwartzBruhat (Fin (n + 1) → F)) (R Rdual : RationalFunctions),
        IsRowFourierPair ψ ν Φ Φhat ∧
        HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R ∧
        HasRationalContinuation q
          (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φhat) Rdual ∧
        NormalizedFunctionalEquation q P Pdual ζ c n m R Rdual

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A type-transport wrapper for the owner's actual unequal-rank integral. -/
def unequalRankIntegralAt (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (f : WhittakerFunctions ψ r) (f' : InverseWhittakerFunctions ψ n) : ℂ → ℂ := by
  subst r
  exact unequalRankIntegral ψ abv j k μ ν f f'

/-- The transformed unequal-rank test uses block `k`, not block `j`, and
right translation by the actual `diag(I_t,w_(r-t))` on the first dual function. -/
def dualUnequalRankModelIntegralAt (hnr : n < r)
    (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) : ℂ → ℂ :=
  unequalRankIntegralAt k j (by omega) (ψ.scale (-1)) abv μ
    (rectangularMeasure ν k (n + 1))
    (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
      (blockWeylAt n r hnr))
    (secondDualFunction ψ n f'.val)

/-- The genuine transformed coefficient family used to specify the dual
normalized generator. All model vectors occur, including their right translates. -/
def dualUnequalRankRationalValuesAt (hnr : n < r)
    (j k : ℕ) (hr : r = n + (j + k + 1))
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    Set RationalFunctions :=
  {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
    ∃ f' : (coefficientModel σ ℓ').toSubmodule,
      HasRationalContinuation q
        (dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ' f f') R}

/-- The constants, the two normalized polynomials and the Laurent exponent
are independent of every allowed rectangular block at the fixed two ranks. -/
def UnequalRankFunctionalEquationConclusion (hnr : n < r)
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) : Prop :=
  ∃ (ζ c : ℂˣ) (m : ℤ) (P Pdual : Polynomial ℂ),
    HasModelMinusOneScalar σ ℓ' ζ ∧
    ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr q ψ abv μ (rectangularMeasure ν j (n + 1))
          π σ ℓ ℓ') P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ') Pdual ∧
      ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ R Rdual : RationalFunctions,
          HasRationalContinuation q
            (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1))
              f.val f'.val) R ∧
          HasRationalContinuation q
            (dualUnequalRankModelIntegralAt hnr j k hr ψ abv μ ν π σ ℓ ℓ' f f') Rdual ∧
          NormalizedFunctionalEquation q P Pdual ζ c r m R Rdual

end UnequalRank

section ValuedTopology

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
private theorem valuative_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

end ValuedTopology

section PadicStatements

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- JPSS Theorem 2.7(iii), equal positive ranks, with the actual plus-sign
Fourier transform and the supplied scalar self-dual Haar measure. -/
def EqualRankFunctionalEquationStatement (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          EqualRankFunctionalEquationConclusion T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ'

/-- JPSS Theorem 2.7(iii), every pair of positive unequal ranks. The same
epsilon monomial works for every `j`, with complementary dual block `k`.
The rectangle measures come from the same self-dual scalar measure. -/
def UnequalRankFunctionalEquationStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := valuative_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ hnr : n < r,
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          UnequalRankFunctionalEquationConclusion hnr T.residueCardinality ψ
            (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ'

end PadicStatements

/-- JPSS Theorem 2.7 over every specified p-adic field and all positive ranks:
parts (i)-(ii) in both rank cases with the common unequal-rank generator, and
part (iii) in both rank cases. The quotient-measure existence is not included. -/
def Theorem27Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    (∀ n, EqualRankAnalyticStatement.{uF, uV, uW} F T n) ∧
    (∀ n j k, UnequalRankAnalyticStatement.{uF, uV, uW} F T n j k) ∧
    (∀ n r, UnequalRankCommonGeneratorStatement.{uF, uV, uW} F T n r) ∧
    (∀ n, EqualRankFunctionalEquationStatement.{uF, uV, uW} F T n) ∧
    (∀ n r, UnequalRankFunctionalEquationStatement.{uF, uV, uW} F T n r)

end Langlands.RankinSelberg
