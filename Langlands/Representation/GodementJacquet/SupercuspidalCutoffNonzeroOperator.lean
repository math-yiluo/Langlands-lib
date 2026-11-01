import Langlands.Representation.GodementJacquet.RegularMatrixZetaOperator
import Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Langlands.Group.GL.CompactOpen

/-! # Nonzero Fourier-regular matrix zeta operators -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped NNReal

universe uF uV

section Conjugation

variable {K : Type uF} [TopologicalSpace K] (d : ℕ)

/-- Pointwise complex conjugation of an actual full-matrix test. -/
def conjugateMatrixTest :
    SchwartzBruhat (Matrix (Fin d) (Fin d) K) →ₗ⋆[ℂ]
      SchwartzBruhat (Matrix (Fin d) (Fin d) K) where
  toFun Φ := ⟨fun A => starRingEnd ℂ (Φ A),
    Φ.locallyConstant.comp (starRingEnd ℂ),
    Φ.hasCompactSupport.comp_left (map_zero (starRingEnd ℂ))⟩
  map_add' Φ Ψ := by
    apply Hecke.TestFunction.ext
    intro A
    exact map_add (starRingEnd ℂ) (Φ A) (Ψ A)
  map_smul' c Φ := by
    apply Hecke.TestFunction.ext
    intro A
    exact map_mul (starRingEnd ℂ) c (Φ A)

@[simp] theorem conjugateMatrixTest_apply
    (Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K))
    (A : Matrix (Fin d) (Fin d) K) :
    conjugateMatrixTest d Φ A = starRingEnd ℂ (Φ A) := rfl

variable [Field K] [MeasurableSpace K]

/-- Conjugation reverses the sign of the actual plus Fourier argument. -/
theorem rectangularFourierIntegral_conjugateMatrixTest
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K))
    (A : Matrix (Fin d) (Fin d) K) :
    rectangularFourierIntegral ψ ν (conjugateMatrixTest d Φ) A =
      starRingEnd ℂ (rectangularFourierIntegral ψ ν Φ (-A)) := by
  unfold rectangularFourierIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with X
  have hpair : rectangularPairing X (-A) = -rectangularPairing X A := by
    simp [rectangularPairing, Finset.sum_neg_distrib]
  have hchar : ψ.complex (-rectangularPairing X A) =
      starRingEnd ℂ (ψ.complex (rectangularPairing X A)) := by
    rw [AddChar.map_neg_eq_inv]
    exact Complex.inv_eq_conj (ψ.norm_complex _)
  simp only [conjugateMatrixTest_apply, hpair, hchar, map_mul, starRingEnd_self_apply]

variable [IsTopologicalDivisionRing K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K] [T2Space K]

/-- Both singular-vanishing conditions are preserved by complex conjugation. -/
theorem conjugate_mem_fourierRegularMatrixTests
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (hsd : IsSelfDual ψ ν)
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    conjugateMatrixTest d Φ ∈ fourierRegularMatrixTests d ψ ν hsd := by
  refine ⟨?_, ?_⟩
  · intro A hA
    simp only [conjugateMatrixTest_apply, hΦ.1 A hA, map_zero]
  · intro A hA
    change rectangularFourierEquiv ψ ν d d hsd (conjugateMatrixTest d Φ) A = 0
    rw [rectangularFourierEquiv_apply,
      rectangularFourierIntegral_conjugateMatrixTest]
    have hneg : ¬ IsUnit (-A) := fun hu => hA (by simpa using hu.neg)
    have hz := hΦ.2 (-A) hneg
    change rectangularFourierEquiv ψ ν d d hsd Φ (-A) = 0 at hz
    rw [rectangularFourierEquiv_apply] at hz
    rw [hz, map_zero]

end Conjugation

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance nonzeroZetaTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance nonzeroZetaValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance nonzeroZetaLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance nonzeroZetaT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance nonzeroZetaDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance nonzeroZetaMeasurable : MeasurableSpace F.Carrier := borel _
local instance nonzeroZetaBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance nonzeroZetaGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance nonzeroZetaGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ} (hm : 0 < m)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
  (hρ : GeneralLinear.IsSupercuspidal ρ)
  (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)

include hm hℓ in
/-- A genuine Fourier-regular test with nonzero zeta operator at every exponent,
provided the smooth coefficient is nonzero at the identity. -/
theorem exists_fourierRegular_nonzero_zetaOperator
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : ℓ v ≠ 0) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∀ s : ℂ,
      regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ ≠ 0 := by
  let T := F.canonicalTopologicalData
  let C := supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v
  have hC : C ∈ fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests
      T hm ψ ν hsd ρ hρ ℓ hℓ v
  let Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    ⟨conjugateMatrixTest (m + 1) C,
      conjugate_mem_fourierRegularMatrixTests (m + 1) ψ ν hsd hC⟩
  let f : GeneralLinear (m + 1) F.Carrier → ℂ := fun g => C g.val
  have hf : Continuous f := C.continuous.comp Units.continuous_val
  have hfc : HasCompactSupport f :=
    hasCompactSupport_restrict_of_mem_regularMatrixTests (m + 1) hC.1
  have hfone : f 1 = ℓ v := by
    change C (1 : GeneralLinear (m + 1) F.Carrier).val = _
    have he := supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v
      (1 : (T.determinantNorm (m + 1)).ker)
    simpa [C] using he
  have hpos : 0 < ∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F.Carrier m :=
    (hf.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      (fun g => sq_nonneg _) (x := 1) (by
        simpa only [Pi.pow_apply, hfone, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hv)
  refine ⟨Φ, fun s hs => ?_⟩
  have heval := regularMatrixZetaOperator_dual F ρ hρ.1.1 s
    ⟨Φ.val, Φ.property.1⟩ v ℓ
  have hi : matrixIntegral F Φ.val s (fun g => ℓ (ρ g v)) =
      ∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F.Carrier m := by
    apply integral_congr_ae
    filter_upwards [] with g
    change starRingEnd ℂ (C g.val) * ℓ (ρ g v) *
      determinantWeight (normalizedAbsoluteValue T) g s = _
    by_cases hg : T.determinantNorm (m + 1) g = 1
    · have hc : C g.val = ℓ (ρ g v) :=
        supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩
      have hw : determinantWeight (normalizedAbsoluteValue T) g s = 1 := by
        change (↑((normalizedAbsoluteValue T) (Matrix.det g.val)) : ℂ) ^ s = 1
        have hnorm : (normalizedAbsoluteValue T) (Matrix.det g.val) = 1 :=
          congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) hg
        rw [hnorm]
        simp
      rw [hw, mul_one, ← hc]
      simpa only [Complex.ofReal_pow] using Complex.conj_mul' (C g.val)
    · have hc : C g.val = 0 :=
        supercuspidalCutoffMatrixTest_apply_of_not_mem T (Nat.succ_pos m)
          ρ hρ ℓ hℓ v g hg
      simp [hc, f]
  have hz : (∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F.Carrier m) = 0 := by
    rw [← hi, ← heval, hs]
    simp
  rw [integral_complex_ofReal] at hz
  have hzreal : (∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F.Carrier m) = 0 :=
    Complex.ofReal_eq_zero.mp hz
  exact hpos.ne' hzreal

/-- Smooth algebraic functionals separate every nonzero vector of the actual
smooth representation of canonical p-adic GL. -/
theorem exists_smoothFunctional_ne_zero (hρsm : IsSmooth ρ)
    (v : V) (hv : v ≠ 0) :
    ∃ ℓ : Module.Dual ℂ V, IsSmoothVector ρ.dual ℓ ∧ ℓ v ≠ 0 := by
  have hcofinal :
      ∀ K : OpenSubgroup (GeneralLinear (m + 1) F.Carrier),
        ∃ L : OpenSubgroup (GeneralLinear (m + 1) F.Carrier),
          IsCompact (L : Set (GeneralLinear (m + 1) F.Carrier)) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hL, hLK⟩ :=
      F.canonicalTopologicalData.generalLinearCompactOpen (m + 1)
        (K : Set (GeneralLinear (m + 1) F.Carrier))
        (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hL, hLK⟩
  have hinj := smoothBidual_injective_of_compact_cofinal hcofinal ρ hρsm
  by_contra h
  push Not at h
  have hz : smoothBidual hρsm v = 0 := by
    apply Subtype.ext
    apply LinearMap.ext
    intro φ
    change φ.val v = 0
    exact h φ.val φ.property
  exact hv (hinj (by simpa only [map_zero] using hz))

include hm hρ in
/-- A nontrivial supercuspidal representation has a single Fourier-regular
matrix test with nonzero actual zeta operator at every complex exponent. -/
theorem exists_fourierRegular_nonzero_zetaOperator_of_nontrivial [Nontrivial V]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∀ s : ℂ,
      regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 v hv
  exact exists_fourierRegular_nonzero_zetaOperator F hm ρ hρ ℓ hℓ ψ ν hsd v hℓv

end Padic

end Langlands.GodementJacquet
