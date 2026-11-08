import Langlands.Representation.RankinSelberg.UniformRankOneTwistTest
import Langlands.Representation.RankinSelberg.UniformRankOneTwistLVanishing
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Classification.ConstituentCompatibility

/-!
# The epsilon monomial of a highly ramified twist

Internal support for the level-uniform form of Jacquet–Shalika 1985,
Proposition (2.2). The Godement–Jacquet functional equation is tested with the
twisted principal test `Φ = 1_{1 + ϖ^j M(O)} · χ⁻¹(det)` against one coefficient
of a ramified `(K_m, χ ∘ det)`-eigenvector. Both zeta integrals are explicit:
the original one is a constant and the dual one is a constant times
`q^(N s)`, `N = (n + 1) a(χ)`. This determines the exponent and the constant of
the epsilon monomial.
-/

noncomputable section

namespace Langlands.RankinSelberg.UniformRankOneTwist

open MeasureTheory HarmonicAnalysis GodementJacquet UniformTwist

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniformTwistEpsilonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance uniformTwistEpsilonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance uniformTwistEpsilonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance uniformTwistEpsilonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance uniformTwistEpsilonMeasurable : MeasurableSpace F.Carrier := borel _
local instance uniformTwistEpsilonBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance uniformTwistEpsilonGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance uniformTwistEpsilonGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abvF" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "μF" => generalLinearHaar F.Carrier

variable {n : ℕ}

section Constants

/-- The dual-side integral `∫ Φ^(g) u(g) |det g|^(n/2) dg` of the twisted principal
test, where `u` is `twistedEpsilonWeight`. -/
def twistedDualIntegral (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ) (χ : Quasicharacter F.Carrier)
    (ω : F.Carrierˣ →* ℂˣ) : ℂ :=
  ∫ g : Langlands.GeneralLinear (n + 1) F.Carrier,
    rectangularFourierIntegral ψ ν
        (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val *
      twistedEpsilonWeight F χ ω g * determinantWeight abvF g (jpssShift n) ∂(μF n)

/-- The constant of the epsilon monomial of a highly ramified twist with central
character `ω`: `J q^((n+1) a(χ)) / vol(K_j)`, with `J = twistedDualIntegral` and
`j = twistLevel a(χ)`. -/
def twistedMatrixEpsilonConstant (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (n : ℕ) (χ : Quasicharacter F.Carrier)
    (ω : F.Carrierˣ →* ℂˣ) : ℂ :=
  twistedDualIntegral F ψ ν n χ ω *
      ((T).residueCardinality : ℂ) ^ ((n + 1) * (T).multiplicativeConductor χ) /
    (((μF n).real (Conductor.principalLevelSubgroup F.Carrier n
      (twistLevel ((T).multiplicativeConductor χ)) :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℝ) : ℂ)

end Constants

section LeftSide

/-- On the general linear group, the principal set `1 + ϖ^j M(O)` is the principal
level subgroup `K_j`. -/
theorem val_mem_principalSet_iff {j : ℕ} (hj : 0 < j)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    g.val ∈ principalSet F n j ↔ g ∈ Conductor.principalLevelSubgroup F.Carrier n j := by
  constructor
  · intro hg
    obtain ⟨E, hE, hEg⟩ := UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup hj
      g.val fun i l => by
        rw [RankOneBox.levelSet_eq_additiveLattice F j]
        exact hg i l
    have hEq : E = g := Units.ext hEg
    exact hEq ▸ hE
  · intro hg i l
    have h := ((UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff g).1 hg).1 i l
    rw [RankOneBox.levelSet_eq_additiveLattice F j] at h
    exact h

/-- The principal level subgroup has positive finite Haar volume. -/
theorem measureReal_principalLevelSubgroup_ne_zero (j : ℕ) :
    (μF n).real (Conductor.principalLevelSubgroup F.Carrier n j :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) ≠ 0 := by
  have hopen : IsOpen (Conductor.principalLevelSubgroup F.Carrier n j :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    (Conductor.principalLevelOpenSubgroup F.Carrier n j).isOpen
  have hpos := hopen.measure_pos (μF n)
    ⟨1, (Conductor.principalLevelSubgroup F.Carrier n j).one_mem⟩
  have hfin := (isCompact_principalLevelSubgroup F (n := n) j).measure_lt_top (μ := μF n)
  rw [Measure.real]
  exact ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin.ne⟩

/-- **The original integrand.** Against a function with `f g = χ(det g) f 1` on
`K_j`, the integrand of the twisted principal test is `f 1` on `K_j` and `0`
elsewhere, at every exponent. -/
theorem matrixIntegrand_twistedPrincipalTest (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ g ∈ Conductor.principalLevelSubgroup F.Carrier n
        (twistLevel ((T).multiplicativeConductor χ)),
      f g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f 1) (s : ℂ) :
    matrixIntegrand abvF (twistedPrincipalTest F n χ) s f =
      (Conductor.principalLevelSubgroup F.Carrier n (twistLevel ((T).multiplicativeConductor χ)) :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)).indicator (fun _ => f 1) := by
  set j := twistLevel ((T).multiplicativeConductor χ) with hj
  funext g
  by_cases hg : g ∈ Conductor.principalLevelSubgroup F.Carrier n j
  · have hdet : g.val.det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
    have hunit : Units.mk0 g.val.det hdet = Matrix.GeneralLinearGroup.det g := Units.ext rfl
    have hw : determinantWeight abvF g s = 1 := by
      rw [determinantWeight, TwoBlock.normalizedAbs_det_eq_one_of_mem F _
        (isCompact_principalLevelSubgroup F j) hg, Complex.ofReal_one, Complex.one_cpow]
    rw [Set.indicator_of_mem hg, matrixIntegrand, twistedPrincipalTest_apply, twistedPrincipalFun,
      Set.indicator_of_mem ((val_mem_principalSet_iff F (twistLevel_pos _) g).2 hg),
      inverseDetTwist_of_ne F χ hdet, hunit, hf g hg, hw, mul_one, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · rw [Set.indicator_of_notMem hg, matrixIntegrand, twistedPrincipalTest_apply,
      twistedPrincipalFun,
      Set.indicator_of_notMem (mt (val_mem_principalSet_iff F (twistLevel_pos _) g).1 hg),
      zero_mul, zero_mul]

/-- **The original zeta integral** of the twisted principal test is the constant
`vol(K_j) f(1)`. -/
theorem matrixIntegral_twistedPrincipalTest (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ g ∈ Conductor.principalLevelSubgroup F.Carrier n
        (twistLevel ((T).multiplicativeConductor χ)),
      f g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f 1) (s : ℂ) :
    matrixIntegral abvF (μF n) (twistedPrincipalTest F n χ) s f =
      (((μF n).real (Conductor.principalLevelSubgroup F.Carrier n
        (twistLevel ((T).multiplicativeConductor χ)) :
          Set (Langlands.GeneralLinear (n + 1) F.Carrier)) : ℝ) : ℂ) * f 1 := by
  have hmeas : MeasurableSet (Conductor.principalLevelSubgroup F.Carrier n
      (twistLevel ((T).multiplicativeConductor χ)) :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)) :=
    (Conductor.principalLevelOpenSubgroup F.Carrier n _).isOpen.measurableSet
  rw [matrixIntegral, matrixIntegrand_twistedPrincipalTest F χ f hf s,
    integral_indicator_const _ hmeas, Complex.real_smul]

end LeftSide

section DualSide

/-- **The dual zeta integral.** If on the support of `Φ^` the inverse transpose of `f`
is `f(1)` times the dual weight and `ord(det g) = -N`, the shifted dual integral is
`f(1) J q^(N s)`, written `f(1) J X^(-N)` in the spectral variable `X = q^(-s)`. -/
theorem matrixIntegral_dual_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (N : ℕ)
    (hdual : ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      rectangularFourierIntegral ψ ν
          (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val ≠ 0 →
        coefficientIota f g = f 1 * twistedEpsilonWeight F χ ω g ∧
          (T).ord (Matrix.det g.val) = -(N : ℤ))
    (ΦHat : MatrixTestFunction n F.Carrier)
    (hΦHat : ∀ x, ΦHat x = rectangularFourierIntegral ψ ν
      (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) x)
    (s : ℂ) :
    matrixIntegral abvF (μF n) ΦHat (s + jpssShift n) (coefficientIota f) =
      f 1 * twistedDualIntegral F ψ ν n χ ω *
        spectralPoint (T).residueCardinality s ^ (-(N : ℤ)) := by
  have hpt : (fun g => matrixIntegrand abvF ΦHat (s + jpssShift n) (coefficientIota f) g) =
      fun g => (f 1 * spectralPoint (T).residueCardinality s ^ (-(N : ℤ))) *
        (rectangularFourierIntegral ψ ν
            (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val *
          twistedEpsilonWeight F χ ω g * determinantWeight abvF g (jpssShift n)) := by
    funext g
    simp only [matrixIntegrand]
    rw [hΦHat]
    by_cases hg : rectangularFourierIntegral ψ ν
        (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val = 0
    · rw [hg]
      ring
    · obtain ⟨h1, h2⟩ := hdual g hg
      rw [h1, Padic.determinantWeight_shift_spectral F g, h2]
      ring
  rw [matrixIntegral, hpt, integral_const_mul, twistedDualIntegral]
  ring

end DualSide

section FunctionalEquation

/-- **The epsilon monomial from one coefficient.** Let `f` be a bi-smooth coefficient
with `f 1 ≠ 0`, `f g = χ(det g) f 1` on `K_j`, and the dual-side pointwise law on the
support of `Φ^`. Then normalized functional-equation data with both polynomials `1`
have exponent `N` and constant `twistedMatrixEpsilonConstant`. -/
theorem epsilon_eq_of_coefficient (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ) {c : ℂˣ} {a : ℤ}
    (hdata : Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c a)
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hfmem : f ∈ biSmoothMatrixCoefficients ρ) (hf1 : f 1 ≠ 0)
    (hfK : ∀ g ∈ Conductor.principalLevelSubgroup F.Carrier n
        (twistLevel ((T).multiplicativeConductor χ)),
      f g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f 1)
    (hdual : ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
      rectangularFourierIntegral ψ ν
          (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) g.val ≠ 0 →
        coefficientIota f g = f 1 * twistedEpsilonWeight F χ ω g ∧
          (T).ord (Matrix.det g.val) =
            -(((n + 1) * (T).multiplicativeConductor χ : ℕ) : ℤ)) :
    a = (((n + 1) * (T).multiplicativeConductor χ : ℕ) : ℤ) ∧
      (c : ℂ) = twistedMatrixEpsilonConstant F ψ ν n χ ω := by
  set q := (T).residueCardinality with hqdef
  have hq1 : 1 < q := (T).residueCardinality_gt_one
  have hq0 : 0 < q := zero_lt_one.trans hq1
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set N := (n + 1) * (T).multiplicativeConductor χ with hNdef
  set K := (Conductor.principalLevelSubgroup F.Carrier n
    (twistLevel ((T).multiplicativeConductor χ)) :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) with hKdef
  have hK : (μF n).real K ≠ 0 := measureReal_principalLevelSubgroup_ne_zero F _
  let f' : biSmoothMatrixCoefficients ρ := ⟨f, hfmem⟩
  obtain ⟨R₀, hR₀⟩ := hdata.1.2.1 (twistedPrincipalTest F n χ) f'
  obtain ⟨ΦHat, hpair, hFE⟩ := hdata.2.2 (twistedPrincipalTest F n χ)
  obtain ⟨RD₀, hRD₀⟩ := hdata.2.1.2.1 ΦHat f'
  have hΦHat : ∀ x, ΦHat x = rectangularFourierIntegral ψ ν
      (twistedPrincipalFun F χ (twistLevel ((T).multiplicativeConductor χ))) x :=
    fun x => (hpair x).2
  set A : ℂ := (((μF n).real K : ℝ) : ℂ) * f 1 with hAdef
  set D : ℂ := f 1 * twistedDualIntegral F ψ ν n χ ω with hDdef
  have hA : A ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hK) hf1
  let R : RationalFunctions := laurentToRatFunc (LaurentPolynomial.C A)
  let RD : RationalFunctions :=
    laurentToRatFunc (LaurentPolynomial.C D * LaurentPolynomial.T (-(N : ℤ)))
  have hR : HasShiftedRationalValue q abvF (μF n) (twistedPrincipalTest F n χ) f R := by
    refine ⟨hR₀.1, 0, fun s _ => ?_⟩
    obtain ⟨hreg, heval⟩ :=
      laurentToRatFunc_regular_and_eval (spectralUnit hq0 s) (LaurentPolynomial.C A)
    rw [coe_spectralUnit] at hreg heval
    refine ⟨hreg, ?_⟩
    rw [heval, laurentEval_C]
    exact matrixIntegral_twistedPrincipalTest F χ f hfK _
  have hRD : HasShiftedRationalValue q abvF (μF n) ΦHat (coefficientIota f) RD := by
    refine ⟨hRD₀.1, 0, fun s _ => ?_⟩
    obtain ⟨hreg, heval⟩ := laurentToRatFunc_regular_and_eval (spectralUnit hq0 s)
      (LaurentPolynomial.C D * LaurentPolynomial.T (-(N : ℤ)))
    rw [coe_spectralUnit] at hreg heval
    refine ⟨hreg, ?_⟩
    rw [heval, map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit]
    exact matrixIntegral_dual_eq F ψ ν χ ω f N hdual ΦHat hΦHat s
  have hfe := hFE f' R RD hR hRD
  -- the functional equation at a spectral parameter
  have key : ∀ s : ℂ, D * ((q : ℂ) * spectralPoint q s) ^ (N : ℤ) =
      (c : ℂ) * spectralPoint q s ^ a * A := by
    intro s
    obtain ⟨hreg, heval⟩ :=
      laurentToRatFunc_regular_and_eval (spectralUnit hq0 s) (LaurentPolynomial.C A)
    obtain ⟨hregD, hevalD⟩ := laurentToRatFunc_regular_and_eval (spectralUnit hq0 (1 - s))
      (LaurentPolynomial.C D * LaurentPolynomial.T (-(N : ℤ)))
    rw [coe_spectralUnit] at hreg heval hregD hevalD
    have h := hfe s hreg hregD
    rw [heval, hevalD, map_mul, laurentEval_C, laurentEval_T, coe_spectralUnit,
      laurentEval_C, Polynomial.eval_one, Polynomial.eval_one, one_mul, one_mul, pow_zero,
      one_mul, epsilonMonomial, spectralPoint_sub_one_sub hq0, ← mul_inv, inv_zpow',
      neg_neg] at h
    rw [h]
  have hX0 : spectralPoint q 0 = 1 := by
    simp [spectralPoint]
  have hX1 : spectralPoint q (-1) = q := by
    simp [spectralPoint]
  have h0 := key 0
  have h1 := key (-1)
  rw [hX0, mul_one, one_zpow, mul_one] at h0
  rw [hX1] at h1
  -- `c A = D q^N`, and then `q^N = q^a`
  have hDq : D * (q : ℂ) ^ (N : ℤ) ≠ 0 := by
    rw [h0]
    exact mul_ne_zero c.ne_zero hA
  have hpow : (q : ℂ) ^ (N : ℤ) = (q : ℂ) ^ a := by
    have h2 : D * (q : ℂ) ^ (N : ℤ) * (q : ℂ) ^ (N : ℤ) =
        D * (q : ℂ) ^ (N : ℤ) * (q : ℂ) ^ a := by
      calc D * (q : ℂ) ^ (N : ℤ) * (q : ℂ) ^ (N : ℤ) = D * ((q : ℂ) * q) ^ (N : ℤ) := by
            rw [mul_zpow]
            ring
        _ = (c : ℂ) * (q : ℂ) ^ a * A := h1
        _ = D * (q : ℂ) ^ (N : ℤ) * (q : ℂ) ^ a := by
            rw [h0]
            ring
    exact mul_left_cancel₀ hDq h2
  have ha : (N : ℤ) = a := by
    have hR' : ((q : ℝ) ^ (N : ℤ) : ℝ) = (q : ℝ) ^ a := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_zpow, Complex.ofReal_zpow, Complex.ofReal_natCast]
      exact hpow
    have hq1' : (1 : ℝ) < q := by exact_mod_cast hq1
    exact zpow_right_injective₀ (zero_lt_one.trans hq1') hq1'.ne' hR'
  refine ⟨ha.symm, ?_⟩
  rw [twistedMatrixEpsilonConstant, eq_div_iff (Complex.ofReal_ne_zero.2 hK)]
  have h0' : (c : ℂ) * A = D * (q : ℂ) ^ (N : ℤ) := h0.symm
  rw [hAdef, hDdef, zpow_natCast] at h0'
  apply mul_left_cancel₀ hf1
  linear_combination h0'

/-- **The epsilon monomial of a highly ramified twist.** Let `ρ` be smooth with central
character `ω`, and let `w ≠ 0` satisfy `ρ(k) w = χ(det k) w` on `K_{m'}`, where
`1 ≤ m'` and `2 m' ≤ a(χ)`. Normalized functional-equation data with both
polynomials `1` then have exponent `(n+1) a(χ)` and constant
`twistedMatrixEpsilonConstant F ψ ν n χ ω`, which depends on nothing else. -/
theorem twistedMatrixEpsilon (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : (T).additiveConductor ψ = 0) (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V) (hρs : IsSmooth ρ)
    (ω : F.Carrierˣ →* ℂˣ) (hω : Classification.HasGLCentralCharacter F.Carrier (n + 1) ρ ω)
    (χ : Quasicharacter F.Carrier) {m' : ℕ} (hm' : 1 ≤ m')
    (hk : 2 * m' ≤ (T).multiplicativeConductor χ) {w : V} (hw0 : w ≠ 0)
    (hw : ∀ y ∈ Conductor.principalLevelSubgroup F.Carrier n m',
      ρ y w = ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) • w)
    {c : ℂˣ} {a : ℤ} (hdata : Padic.NormalizedMatrixFunctionalEquationData F ψ ν ρ 1 1 c a) :
    a = (((n + 1) * (T).multiplicativeConductor χ : ℕ) : ℤ) ∧
      (c : ℂ) = twistedMatrixEpsilonConstant F ψ ν n χ ω := by
  let _ := (T).generalLinearTopologicalGroup (n + 1)
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal
    (GeneralLinear.compactOpen_cofinal F (T) (n + 1)) ρ hρs hw0
  set f := biSmoothCoefficient ρ ℓ ⟨w, hρs w⟩ with hfdef
  have hfg : ∀ g, f g = ℓ.1 (ρ g w) := fun g => rfl
  have hfmem : f ∈ biSmoothMatrixCoefficients ρ := Submodule.subset_span ⟨ℓ, ⟨w, hρs w⟩, rfl⟩
  have hf1w : f 1 = ℓ.1 w := by
    rw [hfg, map_one]
    rfl
  have hf1 : f 1 ≠ 0 := by
    rw [hf1w]
    exact hℓ
  have hfmul : ∀ (z : F.Carrierˣ), ∀ y ∈ Conductor.principalLevelSubgroup F.Carrier n m',
      f (Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) z * y) =
        ((ω z : ℂˣ) : ℂ) * ((χ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * f 1 := by
    intro z y hy
    rw [hfg, hf1w, map_mul, Module.End.mul_apply, hw y hy, hω z, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  have hjm : m' ≤ twistLevel ((T).multiplicativeConductor χ) := by
    unfold twistLevel
    omega
  have hfK : ∀ g ∈ Conductor.principalLevelSubgroup F.Carrier n
      (twistLevel ((T).multiplicativeConductor χ)),
      f g = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * f 1 := by
    intro g hg
    rw [hfg, hf1w, hw g (Conductor.principalLevelSubgroup_antitone F.Carrier n hjm hg), map_smul,
      smul_eq_mul]
  exact epsilon_eq_of_coefficient F ψ ν ρ χ ω hdata f hfmem hf1 hfK
    (fun g hg =>
      UniformTwist.coefficientIota_eq_of_fourierIntegral_ne_zero F ψ hψ ν χ ω hm' hk f hfmul hg)

end FunctionalEquation

end Langlands.RankinSelberg.UniformRankOneTwist
