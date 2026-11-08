import Langlands.LocalFactor.Abelian.ZetaEulerTest
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

/-- The canonical Euler test, using the actual multiplicative conductor. -/
def eulerTest (χ : Character) : TestFunction := by
  classical
  let := T.topology
  exact if ha : T.multiplicativeConductor χ = 0 then cosetTest T 0 0 else
    ⟨(integralUnits T).indicator (fun x => (characterExtension T χ x)⁻¹),
      ramifiedTest_isLocallyConstant T χ ((conductorAt_iff T χ _).mpr rfl) ha,
      ramifiedTest_hasCompactSupport T χ⟩

theorem eulerTest_coe (χ : Character) :
    (eulerTest T χ : F.Carrier → ℂ) =
      if T.multiplicativeConductor χ = 0 then
        (integerRing T).indicator (fun _ => (1 : ℂ)) else
        (integralUnits T).indicator (fun x => (characterExtension T χ x)⁻¹) := by
  classical
  unfold eulerTest
  split_ifs
  · rw [cosetTest_coe, coset_zero, integerRing_eq_lattice_zero]
  · rfl

theorem eulerTest_zero (χ : Character) :
    eulerTest T χ 0 = if T.multiplicativeConductor χ = 0 then 1 else 0 := by
  classical
  rw [show eulerTest T χ 0 = (eulerTest T χ : F.Carrier → ℂ) 0 from rfl, eulerTest_coe]
  split_ifs
  · rw [Set.indicator_of_mem (show (0 : F.Carrier) ∈ integerRing T by
      rw [integerRing_eq_lattice_zero]; exact (T.additiveLattice 0).zero_mem)]
  · exact Set.indicator_of_notMem (fun h => h.1 rfl) _

theorem integralUnit_mul_mem_integerRing (v : F.Carrierˣ)
    (hv : T.ord (v : F.Carrier) = 0) (x : F.Carrier) :
    (v : F.Carrier) * x ∈ integerRing T ↔ x ∈ integerRing T := by
  have hv1 := (mem_integralUnits_iff_valuation T (v : F.Carrier)).mp ⟨v.ne_zero, hv⟩
  rw [integerRing_eq_lattice_zero, SetLike.mem_coe, SetLike.mem_coe,
    T.mem_additiveLattice, T.mem_additiveLattice, map_mul, hv1, one_mul]

theorem integralUnit_mul_mem_integralUnits (v : F.Carrierˣ)
    (hv : T.ord (v : F.Carrier) = 0) (x : F.Carrier) :
    (v : F.Carrier) * x ∈ integralUnits T ↔ x ∈ integralUnits T := by
  have hv1 := (mem_integralUnits_iff_valuation T (v : F.Carrier)).mp ⟨v.ne_zero, hv⟩
  rw [mem_integralUnits_iff_valuation, mem_integralUnits_iff_valuation,
    map_mul, hv1, one_mul]

/-- Multiplication by an integral unit has inverse-character covariance. -/
theorem eulerTest_mul_integralUnit (χ : Character) (v : F.Carrierˣ)
    (hv : T.ord (v : F.Carrier) = 0) (x : F.Carrier) :
    eulerTest T χ (x * v) = (χ v : ℂ)⁻¹ * eulerTest T χ x := by
  classical
  rw [show eulerTest T χ (x * v) = (eulerTest T χ : F.Carrier → ℂ) (x * v) from rfl,
    show eulerTest T χ x = (eulerTest T χ : F.Carrier → ℂ) x from rfl, eulerTest_coe]
  by_cases ha : T.multiplicativeConductor χ = 0
  · rw [ite_eq_left ha]
    have hχv : (χ v : ℂ) = 1 := by
      have hχ := ((conductorAt_iff T χ 0).mpr ha.symm).1 v
      exact congrArg Units.val (hχ (by simpa [unitLevel] using hv))
    rw [hχv, inv_one, one_mul, mul_comm x]
    simp only [Set.indicator_apply, integralUnit_mul_mem_integerRing T v hv]
  · rw [ite_eq_right ha, mul_comm x]
    by_cases hx : x ∈ integralUnits T
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((integralUnit_mul_mem_integralUnits T v hv x).mpr hx),
        characterExtension_unit_mul, mul_inv]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h => hx ((integralUnit_mul_mem_integralUnits T v hv x).mp h)),
        mul_zero]

/-- The plus Fourier transform has the dual integral-unit covariance. -/
theorem fourier_eulerTest_mul_integralUnit (χ : Character) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (v : F.Carrierˣ) (hv : T.ord (v : F.Carrier) = 0)
    (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) (y * v) =
      (χ v : ℂ) * HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have habs : T.normalizedAbs (v : F.Carrier) = 1 := by
    rw [T.normalizedAbs_of_ne_zero v.ne_zero, hv, neg_zero, zpow_zero]
  have h := integral_comp_mul_scalar T μ v
    (fun x => ψ.complex (x * y) * eulerTest T χ x)
  rw [habs, inv_one, one_smul] at h
  have hfun :
      (fun x => ψ.complex ((v : F.Carrier) * x * y) * eulerTest T χ ((v : F.Carrier) * x)) =
        (fun x => (χ v : ℂ)⁻¹ * (ψ.complex (x * (y * v)) * eulerTest T χ x)) := by
    funext x
    rw [mul_comm (v : F.Carrier) x, eulerTest_mul_integralUnit T χ v hv,
      show x * (v : F.Carrier) * y = x * (y * v) by ring]
    ring
  rw [hfun, integral_const_mul] at h
  change _ = (χ v : ℂ) * ∫ x, ψ.complex (x * y) * eulerTest T χ x ∂μ.measure
  rw [← h, ← mul_assoc, mul_inv_cancel₀ (χ v).ne_zero, one_mul]
  rfl

/-- Unramified tests transform to the additive-conductor lattice indicator. -/
theorem fourier_eulerTest_unramified (χ : Character)
    (hχ : T.multiplicativeConductor χ = 0) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) y =
      ((μ.measure (integerRing T)).toReal : ℂ) *
        (T.additiveLattice (T.additiveConductor ψ) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  change HarmonicAnalysis.fourierIntegral ψ μ (eulerTest T χ) y = _
  rw [eulerTest_coe, ite_eq_left hχ, integerRing_eq_lattice_zero]
  have h := (HarmonicAnalysis.padicLatticeFourier F T ψ μ 0 0 y).2
  rw [coset_zero] at h
  simpa only [sub_zero, zero_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one] using h

/-- At conductor zero and integer-ring mass one, the unramified test is fixed. -/
theorem fourier_eulerTest_eq_self (χ : Character)
    (hχ : T.multiplicativeConductor χ = 0) (ψ : AdditiveCharacter)
    (hψ : letI := T.topology; T.additiveConductor ψ = 0) (μ : LocalHaar)
    (hμ : letI := T.topology; letI := borel F.Carrier;
      (μ.measure (integerRing T)).toReal = 1) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) =
      (eulerTest T χ : F.Carrier → ℂ) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  funext y
  rw [fourier_eulerTest_unramified T χ hχ ψ μ y, hψ, hμ, Complex.ofReal_one, one_mul,
    eulerTest_coe, ite_eq_left hχ, integerRing_eq_lattice_zero]

/-- Ramified tests transform to the explicit Gauss-conductor shell. -/
theorem fourier_eulerTest_ramified (χ : Character)
    (hχ : T.multiplicativeConductor χ ≠ 0) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (y : F.Carrier) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ) y =
      (gaussShell T (T.additiveConductor ψ + T.multiplicativeConductor χ)).indicator
        (fun z =>
          Complex.exp (-((T.additiveConductor ψ +
            (T.multiplicativeConductor χ : ℤ) : ℤ) : ℂ) *
              (Real.log (T.residueCardinality : ℝ) : ℂ)) *
            epsilon T χ ψ μ.measure 0 * characterExtension T χ z) y := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  change HarmonicAnalysis.fourierIntegral ψ μ (eulerTest T χ) y = _
  rw [eulerTest_coe, ite_eq_right hχ]
  simpa only [HarmonicAnalysis.fourierIntegral,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, epsilon, epsilonAt,
    ite_eq_right hχ] using
      fourier_ramifiedTest T μ χ ((conductorAt_iff T χ _).mpr rfl) hχ ψ.toAddChar
        ((additiveConductorAt_iff T ψ _).mpr rfl) y

end Langlands.LocalFactor.PadicAbelian
