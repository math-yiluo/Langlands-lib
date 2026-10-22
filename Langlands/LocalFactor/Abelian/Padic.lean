import Langlands.LocalFactor.Abelian.Definitions
import Langlands.LocalField.Uniformizer
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Finsupp.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Callable rank-one local-factor expressions

Concrete expressions for the abelian theorem family, using the actual
conductors constructed by `Langlands.HarmonicAnalysis.Conductor`.
No functional equation or nonabelian constant system is assumed or chosen.

Worker 33 authored the callable expressions and conductor bridges. Worker 20
connects them to the convergent abelian construction and supplies rational
L-factors with restricted evaluation.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- The existing measure type with precisely the supplied topology's Borel
measurable space. This abbreviation introduces no new measure structure. -/
abbrev BorelMeasure :=
  letI := T.topology
  letI := borel F.Carrier
  Measure F.Carrier

/-- The actual valuation integer ring as a subset of the field. -/
def integerRing : Set F.Carrier :=
  Set.range (fun x : T.Integers => (x : F.Carrier))

/-- The nonzero elements of order zero in the actual field. -/
def integralUnits : Set F.Carrier := {x | x ≠ 0 ∧ T.ord x = 0}

/-- The spectral variable uses the actual residue cardinality. -/
def spectralVariable (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (T.residueCardinality : ℝ) : ℂ))

/-- A quasicharacter extended by zero at the origin. -/
def characterExtension (χ : MultiplicativeCharacter) (x : F.Carrier) : ℂ := by
  classical
  exact if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)

/-- The valuation formula for a unit-filtration level, including level zero. -/
def unitLevel (a : ℕ) (v : F.Carrierˣ) : Prop :=
  if a = 0 then T.ord (v : F.Carrier) = 0 else
    T.discreteValuation ((v : F.Carrier) - 1) ≤ WithZero.exp (-(a : ℤ))

private theorem ord_unit_zero_iff (v : F.Carrierˣ) :
    T.ord (v : F.Carrier) = 0 ↔ T.discreteValuation (v : F.Carrier) = 1 := by
  constructor
  · intro h
    have hn : T.discreteValuation (v : F.Carrier) ≠ 0 :=
      (map_ne_zero T.discreteValuation).mpr (Units.ne_zero v)
    have hl : WithZero.log (T.discreteValuation (v : F.Carrier)) = 0 :=
      neg_eq_zero.mp h
    have he := WithZero.exp_log hn
    simpa [hl] using he.symm
  · intro h
    simp [PadicField.TopologicalData.ord, h]

/-- The local formula is exactly membership in the owner's actual principal units. -/
theorem unitLevel_iff_mem_principalUnits (a : ℕ) (v : F.Carrierˣ) :
    unitLevel T a v ↔ v ∈ T.principalUnits a := by
  by_cases ha : a = 0
  · subst a
    simpa [unitLevel, T.mem_principalUnits_zero] using ord_unit_zero_iff T v
  · simp only [unitLevel, ite_eq_right ha, T.mem_principalUnits]
    constructor
    · intro h
      have hlt : T.discreteValuation ((v : F.Carrier) - 1) < 1 :=
        h.trans_lt (by
          simpa using (WithZero.exp_lt_exp.mpr (show -(a : ℤ) < 0 by omega)))
      refine ⟨?_, h⟩
      have he := T.discreteValuation.map_add_eq_of_lt_right
        (x := (v : F.Carrier) - 1) (y := 1) (by simpa using hlt)
      simpa using he
    · exact fun h => h.2

/-- The least-level characterization used in the abelian theorem target. -/
def ConductorAt (χ : MultiplicativeCharacter) (a : ℕ) : Prop :=
  IsLeast {b : ℕ | ∀ v : F.Carrierˣ, unitLevel T b v → χ v = 1} a

/-- The predicate names precisely the already constructed conductor. -/
theorem conductorAt_iff (χ : MultiplicativeCharacter) (a : ℕ) :
    ConductorAt T χ a ↔ a = T.multiplicativeConductor χ := by
  have ht (b : ℕ) :
      (∀ v : F.Carrierˣ, unitLevel T b v → χ v = 1) ↔
        T.MultiplicativeTrivialAt χ b := by
    simp only [unitLevel_iff_mem_principalUnits,
      PadicField.TopologicalData.MultiplicativeTrivialAt]
  have hc : ConductorAt T χ (T.multiplicativeConductor χ) := by
    refine ⟨(ht _).mpr (T.multiplicativeConductor_spec χ), ?_⟩
    intro b hb
    exact (T.multiplicativeTrivialAt_iff_conductor_le χ b).mp ((ht b).mp hb)
  exact ⟨fun h => h.unique hc, fun h => h.symm ▸ hc⟩

/-- The greatest-level characterization, with zero included via the valuation. -/
def AdditiveConductorAt (ψ : AddChar F.Carrier Circle) (n : ℤ) : Prop :=
  IsGreatest {m : ℤ | ∀ x : F.Carrier,
    T.discreteValuation x ≤ WithZero.exp m → ψ x = 1} n

/-- The additive predicate names precisely the owner's constructed conductor. -/
theorem additiveConductorAt_iff (ψ : AdditiveCharacter) (n : ℤ) :
    letI := T.topology
    AdditiveConductorAt T ψ.toAddChar n ↔ n = T.additiveConductor ψ := by
  let := T.topology
  have hc : AdditiveConductorAt T ψ.toAddChar (T.additiveConductor ψ) :=
    T.additiveConductor_spec ψ
  exact ⟨fun h => h.unique hc, fun h => h.symm ▸ hc⟩

/-- The elementary Euler expression, retaining its explicit conductor input.
The public `lFactor` below uses the owner's actual conductor constructor. -/
def lFactorAt (π : F.Carrierˣ) (χ : MultiplicativeCharacter)
    (a : ℕ) (s : ℂ) : ℂ :=
  if a = 0 then (1 - (χ π : ℂ) * spectralVariable T s)⁻¹ else 1

/-- The domain on which the Euler expression is a legitimate finite value. -/
def RegularPoint (π : F.Carrierˣ) (χ : MultiplicativeCharacter)
    (a : ℕ) (s : ℂ) : Prop :=
  a ≠ 0 ∨ 1 - (χ π : ℂ) * spectralVariable T s ≠ 0

/-- The half-plane of absolute convergence of the rank-one zeta integral. -/
def ConvergesAt (π : F.Carrierˣ) (χ : MultiplicativeCharacter) (s : ℂ) : Prop :=
  ‖(χ π : ℂ)‖ * Real.exp (-s.re * Real.log (T.residueCardinality : ℝ)) < 1

/-- The additive-Haar integrand, with value zero at zero. -/
def zetaIntegrand (f : F.Carrier → ℂ) (χ : MultiplicativeCharacter)
    (s : ℂ) (x : F.Carrier) : ℂ := by
  classical
  exact if x = 0 then 0 else
    f x * characterExtension T χ x *
      Complex.exp ((s - 1) * (Real.log (T.normalizedAbs x) : ℂ))

/-- The raw Bochner zeta integral; integrability is a separate theorem. -/
def zeta (μ : BorelMeasure T) (f : F.Carrier → ℂ)
    (χ : MultiplicativeCharacter) (s : ℂ) : ℂ :=
  letI := T.topology
  letI := borel F.Carrier
  ∫ x, zetaIntegrand T f χ s x ∂μ

/-- A normal meromorphic representative extending the actual convergent integral.
This predicate does not assume or choose such a representative. -/
def ExtendsIntegral (π : F.Carrierˣ) (μ : BorelMeasure T)
    (f : F.Carrier → ℂ) (χ : MultiplicativeCharacter) (Z : ℂ → ℂ) : Prop :=
  MeromorphicNFOn Z Set.univ ∧
    ∀ s, ConvergesAt T π χ s → Z s = zeta T μ f χ s

/-- Evaluation of the finite Laurent numerator in the actual variable `q^(-s)`. -/
def laurentEvaluation (A : ℤ →₀ ℂ) (s : ℂ) : ℂ :=
  A.sum (fun k c =>
    c * Complex.exp (-(k : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)))

/-- The plus-character Gauss integrand. Its use below is on an annulus excluding zero. -/
def gaussIntegrand (χ : MultiplicativeCharacter) (ψ : AddChar F.Carrier Circle)
    (s : ℂ) (x : F.Carrier) : ℂ :=
  (characterExtension T χ x)⁻¹ *
    Complex.exp (-s * (Real.log (T.normalizedAbs x) : ℂ)) * (ψ x : ℂ)

/-- The actual annulus of elements of order `-d`. -/
def gaussShell (d : ℤ) : Set F.Carrier := {x | x ≠ 0 ∧ T.ord x = -d}

/-- Tate's explicit fixed-Haar epsilon expression at specified conductor levels.
Only the constructor `epsilon` below supplies the actual conductor values.
The unramified formula includes the additive conductor and Haar volume. -/
def epsilonAt (π : F.Carrierˣ) (χ : MultiplicativeCharacter)
    (ψ : AddChar F.Carrier Circle) (μ : BorelMeasure T)
    (a : ℕ) (n : ℤ) (s : ℂ) : ℂ :=
  letI := T.topology
  letI := borel F.Carrier
  if a = 0 then
    (χ π : ℂ) ^ n *
      Complex.exp ((n : ℂ) * (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
      (μ (integerRing T)).toReal
  else ∫ x in gaussShell T (n + a), gaussIntegrand T χ ψ s x ∂μ

/-- A raw representative of the abelian L expression. Its totalized value at a
denominator zero is not an analytic value. Use `rationalLFactor` for the factor
and `regularLValue` for numerical evaluation. -/
def lFactor (χ : MultiplicativeCharacter) (s : ℂ) : ℂ :=
  lFactorAt T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s

/-- The actual fixed-Haar rank-one epsilon expression. Its conductors are chosen
only from the owner's proved least/greatest-level existence theorems. -/
def epsilon (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : BorelMeasure T) (s : ℂ) : ℂ :=
  letI := T.topology
  epsilonAt T (uniformizerUnit T) χ ψ.toAddChar μ
    (T.multiplicativeConductor χ) (T.additiveConductor ψ) s

/-- The unshifted local constant, keeping the Haar measure as an input. -/
def deligneConstant (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : BorelMeasure T) : ℂ :=
  epsilon T χ ψ μ 0

/-- The centered value, still at the supplied Haar measure.
This definition does not replace that measure by a self-dual one. -/
def centeredConstant (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : BorelMeasure T) : ℂ :=
  epsilon T χ ψ μ (1 / 2)

section Rational

open Polynomial

/-- The actual rank-one Euler denominator, with constant term one. -/
def lPolynomial (χ : MultiplicativeCharacter) : ℂ[X] :=
  if T.multiplicativeConductor χ = 0 then
    1 - C (χ (uniformizerUnit T) : ℂ) * X
  else 1

@[simp] theorem lPolynomial_coeff_zero (χ : MultiplicativeCharacter) :
    (lPolynomial T χ).coeff 0 = 1 := by
  classical
  by_cases h : T.multiplicativeConductor χ = 0 <;> simp [lPolynomial, h]

theorem lPolynomial_ne_zero (χ : MultiplicativeCharacter) :
    lPolynomial T χ ≠ 0 := by
  intro h
  have hc := lPolynomial_coeff_zero T χ
  rw [h, coeff_zero] at hc
  exact zero_ne_one hc

/-- The rank-one L-factor in the rational function field. Poles are retained. -/
def rationalLFactor (χ : MultiplicativeCharacter) : RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ) (lPolynomial T χ))⁻¹

theorem rationalLFactor_ne_zero (χ : MultiplicativeCharacter) :
    rationalLFactor T χ ≠ 0 :=
  inv_ne_zero (RatFunc.algebraMap_ne_zero (lPolynomial_ne_zero T χ))

theorem rationalLFactor_mul_denominator (χ : MultiplicativeCharacter) :
    rationalLFactor T χ * algebraMap ℂ[X] (RatFunc ℂ) (lPolynomial T χ) = 1 :=
  inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero (lPolynomial_ne_zero T χ))

theorem regularPoint_iff_polynomial_ne_zero (χ : MultiplicativeCharacter) (s : ℂ) :
    RegularPoint T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s ↔
      (lPolynomial T χ).eval (spectralVariable T s) ≠ 0 := by
  classical
  by_cases h : T.multiplicativeConductor χ = 0 <;>
    simp [RegularPoint, lPolynomial, h]

/-- Evaluation of the rational factor, only at a regular spectral point. -/
def regularLValue (χ : MultiplicativeCharacter)
    (s : {s : ℂ // RegularPoint T (uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s}) : ℂˣ :=
  (Units.mk0 ((lPolynomial T χ).eval (spectralVariable T s.val))
    ((regularPoint_iff_polynomial_ne_zero T χ s.val).mp s.property))⁻¹

theorem coe_regularLValue (χ : MultiplicativeCharacter)
    (s : {s : ℂ // RegularPoint T (uniformizerUnit T) χ
      (T.multiplicativeConductor χ) s}) :
    (regularLValue T χ s : ℂ) = lFactor T χ s.val := by
  classical
  change ((lPolynomial T χ).eval (spectralVariable T s.val))⁻¹ = _
  by_cases h : T.multiplicativeConductor χ = 0 <;>
    simp [lPolynomial, lFactor, lFactorAt, h]

end Rational

section ConstructionBridges

local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

theorem characterExtension_eq_extendZero (χ : MultiplicativeCharacter) :
    letI := T.topology
    characterExtension T χ = HarmonicAnalysis.Quasicharacter.extendZero χ := rfl

theorem integerRing_eq : integerRing T = (T.Integers : Set F.Carrier) := by
  ext x
  simp [integerRing]

/-- The order annulus is exactly the valuation shell used in the proved
convergent Gauss construction. -/
theorem gaussShell_eq_valuationShell (d : ℤ) :
    gaussShell T d = T.valuationShell d := by
  ext x
  constructor
  · rintro ⟨hx, ho⟩
    have hv : T.discreteValuation x ≠ 0 := (map_ne_zero _).mpr hx
    have hl : WithZero.log (T.discreteValuation x) = d := by
      simpa only [PadicField.TopologicalData.ord, neg_inj] using ho
    change T.discreteValuation x = WithZero.exp d
    rw [← hl, WithZero.exp_log hv]
  · intro hx
    refine ⟨T.valuationShell_ne_zero d hx, ?_⟩
    change -WithZero.log (T.discreteValuation x) = -d
    change T.discreteValuation x = WithZero.exp d at hx
    simp [hx]

theorem gaussIntegrand_zero (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) :
    letI := T.topology
    gaussIntegrand T χ ψ.toAddChar 0 =
      HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ := by
  let := T.topology
  funext x
  simp only [gaussIntegrand, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  rfl

theorem normalizedAbs_on_gaussShell (d : ℤ) {x : F.Carrier}
    (hx : x ∈ gaussShell T d) :
    T.normalizedAbs x = (T.residueCardinality : ℝ) ^ d := by
  simp [PadicField.TopologicalData.normalizedAbs, hx.1, hx.2]

/-- On its shell the spectral Gauss integrand is a constant multiple of the
continuous unshifted integrand. -/
theorem gaussIntegrand_on_shell (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (d : ℤ) (s : ℂ) {x : F.Carrier} (hx : x ∈ gaussShell T d) :
    letI := T.topology
    gaussIntegrand T χ ψ.toAddChar s x =
      Complex.exp (-s * (Real.log ((T.residueCardinality : ℝ) ^ d) : ℂ)) *
        HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ x := by
  let := T.topology
  rw [gaussIntegrand, normalizedAbs_on_gaussShell T d hx]
  rw [characterExtension_eq_extendZero]
  change _ * _ * (ψ.toAddChar x : ℂ) = _ * (_ * (ψ.toAddChar x : ℂ))
  ring

/-- The actual spectral Gauss integral converges for every complex parameter.
This is an intrinsic compact-shell construction result, not a functional equation. -/
theorem gaussIntegrand_integrable (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (d : ℤ) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    IntegrableOn (gaussIntegrand T χ ψ.toAddChar s) (gaussShell T d) μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hi : IntegrableOn (HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ)
      (gaussShell T d) μ.measure := by
    rw [gaussShell_eq_valuationShell]
    exact ContinuousOn.integrableOn_compact'
      (T.valuationShell_compact_closed d).1
      (T.valuationShell_compact_closed d).2.measurableSet
      ((HarmonicAnalysis.Quasicharacter.continuousOn_epsilonIntegrand χ ψ).mono
        (fun _x hx => T.valuationShell_ne_zero d hx))
  exact IntegrableOn.congr_fun (hi.const_mul _)
    (fun x hx => (gaussIntegrand_on_shell T χ ψ d s hx).symm)
    (by rw [gaussShell_eq_valuationShell]; exact
      (T.valuationShell_compact_closed d).2.measurableSet)

private theorem residueCardinality_pos : 0 < (T.residueCardinality : ℝ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact Nat.cast_pos.mpr (show 0 < Nat.card
    (IsLocalRing.ResidueField (ValuativeRel.valuation F.Carrier).integer) from Nat.card_pos)

private theorem exp_log_residue_int_mul (n : ℤ) :
    Complex.exp ((n : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
      (T.residueCardinality : ℂ) ^ n := by
  rw [Complex.exp_int_mul, ← Complex.ofReal_exp,
    Real.exp_log (residueCardinality_pos T)]
  simp only [Complex.ofReal_natCast]

/-- The spectral expression at zero is exactly the convergent, scale-independent
constant already constructed in `Abelian`. No functional equation is used. -/
theorem deligneConstant_eq_abelianEpsilonExpression
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    deligneConstant T χ ψ μ.measure = T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  classical
  by_cases h : T.multiplicativeConductor χ = 0
  · have hχ := (T.multiplicativeConductor_eq_zero_iff χ).mp h
    rw [T.abelianEpsilonExpression_unramified_scale χ ψ μ hχ
      (uniformizerUnit T ^ T.additiveConductor ψ)
      (uniformizerUnit_zpow_value T _), uniformizerUnit_zpow_abs]
    simp only [deligneConstant, epsilon, epsilonAt, h, ite_true, sub_zero, mul_one,
      exp_log_residue_int_mul, integerRing_eq, map_zpow, Units.val_zpow_eq_zpow_val,
      PadicField.TopologicalData.integerVolume,
      measureReal_def, Complex.ofReal_inv, Complex.ofReal_zpow, Complex.ofReal_natCast,
      zpow_neg, div_inv_eq_mul]
  · have hχ := mt (T.multiplicativeConductor_eq_zero_iff χ).mpr h
    rw [T.abelianEpsilonExpression_ramified χ ψ μ hχ]
    simp only [deligneConstant, epsilon, epsilonAt, h, ite_false,
      gaussIntegrand_zero, gaussShell_eq_valuationShell,
      PadicField.TopologicalData.abelianGaussIntegral,
      PadicField.TopologicalData.epsilonShell]

/-- Actual Haar measures satisfying the intrinsic Fourier self-duality predicate.
This subtype does not assert that such a measure exists. -/
def SelfDualHaar (ψ : AdditiveCharacter) :=
  {μ : LocalHaar //
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
    letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
    letI : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.IsSelfDual ψ μ}

/-- Langlands' half-shifted rank-one constant at a supplied self-dual measure.
No self-dual measure is chosen and no existence theorem is assumed. -/
def langlandsConstantAtSelfDual (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : SelfDualHaar T ψ) : ℂ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  centeredConstant T χ ψ μ.val.measure

/-- Langlands' spectral epsilon expression at a supplied self-dual measure.
In the Deligne spectral convention this is evaluated at `s`, not `s + 1/2`. -/
def langlandsEpsilonAtSelfDual (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : SelfDualHaar T ψ) (s : ℂ) : ℂ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  epsilon T χ ψ μ.val.measure s

theorem langlandsEpsilonAtSelfDual_half (χ : MultiplicativeCharacter)
    (ψ : AdditiveCharacter) (μ : SelfDualHaar T ψ) :
    langlandsEpsilonAtSelfDual T χ ψ μ (1 / 2) =
      langlandsConstantAtSelfDual T χ ψ μ := rfl

end ConstructionBridges

end Langlands.LocalFactor.PadicAbelian
