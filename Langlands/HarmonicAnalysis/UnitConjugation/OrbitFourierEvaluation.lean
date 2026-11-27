import Langlands.HarmonicAnalysis.Bicharacter.CompactOpenDuality
import Langlands.HarmonicAnalysis.Distribution.Haar
import Langlands.HarmonicAnalysis.UnitConjugation.FourierCosetTests
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitProjection

/-! # Evaluation of a lattice character orbit by an invariant distribution -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory Set
open Hecke.TestFunction (characteristic pullback pullback_apply)

variable {R : Type*} [NormedRing R] {e : R → R → ℂ} (he : IsSelfDualBicharacter e)
  (L : AddSubgroup R) (hLo : IsOpen (L : Set R)) (hLc : IsCompact (L : Set R))

/-- The character `x ↦ e x z` on `L`, extended by zero. -/
def latticeCharacterTest (z : R) : SchwartzBruhat R :=
  Distribution.multiplyTest
    ⟨fun x => e x z, he.isLocallyConstant.comp_continuous (continuous_id.prodMk continuous_const)⟩
    (characteristic ⟨L.isClosed_of_isOpen hLo, hLo⟩ hLc)

@[simp] theorem latticeCharacterTest_apply (z x : R) :
    latticeCharacterTest he L hLo hLc z x = (L : Set R).indicator (fun x => e x z) x := by
  rw [latticeCharacterTest, Distribution.multiplyTest_apply]
  change e x z * (L : Set R).indicator (fun _ => (1 : ℂ)) x = _
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx, indicator_of_mem hx, mul_one]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

private theorem latticeCharacterTest_add_annihilator (z a : R)
    (ha : a ∈ he.annihilator (L : Set R)) :
    latticeCharacterTest he L hLo hLc (z + a) = latticeCharacterTest he L hLo hLc z := by
  apply Hecke.TestFunction.ext
  intro x
  simp only [latticeCharacterTest_apply]
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx, indicator_of_mem hx, he.map_add_right,
      he.mem_annihilator.mp ha x hx, mul_one]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

private theorem latticeCharacterTest_conjugation (K : Subgroup Rˣ)
    (hKL : ∀ k ∈ K, ∀ x ∈ L, conjugationHomeomorph k x ∈ L)
    (hKe : ∀ k ∈ K, ∀ x z, e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z)
    (k : Rˣ) (hk : k ∈ K) (z : R) :
    latticeCharacterTest he L hLo hLc (conjugationHomeomorph k z) =
      pullback (conjugationHomeomorph k⁻¹) (latticeCharacterTest he L hLo hLc z) := by
  apply Hecke.TestFunction.ext
  intro x
  simp only [pullback_apply, latticeCharacterTest_apply]
  have hcancel : conjugationHomeomorph k (conjugationHomeomorph k⁻¹ x) = x := by
    rw [← conjugationHomeomorph_mul, mul_inv_cancel, conjugationHomeomorph_one]
  have hmem : conjugationHomeomorph k⁻¹ x ∈ L ↔ x ∈ L :=
    ⟨fun h => hcancel ▸ hKL k hk _ h, hKL k⁻¹ (K.inv_mem hk) x⟩
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
    simpa only [hcancel] using hKe k hk (conjugationHomeomorph k⁻¹ x) z
  · rw [indicator_of_notMem hx, indicator_of_notMem (hmem.not.mpr hx)]

variable [compactR : LocallyCompactSpace R] [countableR : SecondCountableTopology R]
  [exhaustionR : CompactOpenExhaustion R]
  [MeasurableSpace R] [BorelSpace R] (μ : Measure R) [μ.IsAddHaarMeasure]

/-- The Fourier transform of the coset test for the dual lattice is the
corresponding lattice character test times the volume of the dual lattice. -/
theorem fourierDualCoset_eq_latticeCharacterTest (z : R) :
    bicharacterFourierSB μ he (latticeCosetTest (he.annihilator (L : Set R))
      (he.isOpen_annihilator hLc) (he.isCompact_annihilator_compactOpen L hLo hLc) z) =
      (μ.real (he.annihilator (L : Set R) : Set R) : ℂ) • latticeCharacterTest he L hLo hLc z := by
  let A := he.annihilator (L : Set R)
  have hAo : IsOpen (A : Set R) := he.isOpen_annihilator hLc
  have hAc : IsCompact (A : Set R) := he.isCompact_annihilator_compactOpen L hLo hLc
  apply Hecke.TestFunction.ext
  intro x
  change bicharacterFourierSB μ he (latticeCosetTest A hAo hAc z) x =
    (μ.real A : ℂ) * latticeCharacterTest he L hLo hLc z x
  rw [fourierLatticeCoset μ he A hAo hAc,
    show he.annihilator (A : Set R) = L from compactOpenDoubleAnnihilator he L μ hLo hLc,
    latticeCharacterTest_apply]
  by_cases hx : x ∈ L
  · rw [indicator_of_mem hx, indicator_of_mem hx, mul_comm]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

/-- A finite character sum in one conjugation orbit of dual-lattice cosets has
an evaluation given by the Fourier-side evaluation at any of those cosets. -/
def OrbitFourierEvaluationStatement [LocallyCompactSpace R] [SecondCountableTopology R]
    [CompactOpenExhaustion R] {I : Type*} (K : Subgroup Rˣ) (J : Finset I)
    (a : R) (z : I → R) (c : ℂ) (T : Distribution R) (χ : SchwartzBruhat R) : Prop :=
  let A := he.annihilator (L : Set R)
  let f := latticeCosetTest A (he.isOpen_annihilator hLc)
    (he.isCompact_annihilator_compactOpen L hLo hLc) a
  (∀ k ∈ K, ∀ x ∈ L, conjugationHomeomorph k x ∈ L) →
  (∀ k ∈ K, ∀ x y, e (conjugationHomeomorph k x) (conjugationHomeomorph k y) = e x y) →
  IsConjugationInvariant T →
  (∀ i ∈ J, z i ∈ conjugationCosetOrbit K A a) →
  χ = c • ∑ i ∈ J, latticeCharacterTest he L hLo hLc (z i) →
  (μ.real A : ℂ) * T χ = (c * (J.card : ℂ)) * T (bicharacterFourierSB μ he f) ∧
    (c ≠ 0 → J.Nonempty → (T χ = 0 ↔ T (bicharacterFourierSB μ he f) = 0))

theorem orbitFourierEvaluation {I : Type*} (K : Subgroup Rˣ) (J : Finset I)
    (a : R) (z : I → R) (c : ℂ) (T : Distribution R) (χ : SchwartzBruhat R) :
    OrbitFourierEvaluationStatement he L hLo hLc μ K J a z c T χ := by
  dsimp only [OrbitFourierEvaluationStatement]
  intro hKL hKe hInv hz hχ
  let A := he.annihilator (L : Set R)
  have hAo : IsOpen (A : Set R) := he.isOpen_annihilator hLc
  have hAc : IsCompact (A : Set R) := he.isCompact_annihilator_compactOpen L hLo hLc
  let f := latticeCosetTest A hAo hAc a
  have hValue (i : I) (hi : i ∈ J) : T (latticeCharacterTest he L hLo hLc (z i)) =
      T (latticeCharacterTest he L hLo hLc a) := by
    obtain ⟨k, hk, l, hl, hki⟩ := hz i hi
    rw [hki, latticeCharacterTest_add_annihilator he L hLo hLc _ _ hl,
      latticeCharacterTest_conjugation he L hLo hLc K hKL hKe k hk]
    exact (isConjugationInvariant_iff T).mp hInv k⁻¹ _
  have hSum : T χ = (c * (J.card : ℂ)) * T (latticeCharacterTest he L hLo hLc a) := by
    rw [hχ, map_smul, smul_eq_mul, map_sum,
      Finset.sum_congr rfl hValue, Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hFourier : T (bicharacterFourierSB μ he f) =
      (μ.real A : ℂ) * T (latticeCharacterTest he L hLo hLc a) := by
    rw [show bicharacterFourierSB μ he f = _ from fourierDualCoset_eq_latticeCharacterTest he L hLo hLc μ a,
      map_smul, smul_eq_mul]
  have h := calc
    (μ.real A : ℂ) * T χ = (μ.real A : ℂ) * ((c * (J.card : ℂ)) * T (latticeCharacterTest he L hLo hLc a)) := by
      rw [hSum]
    _ = (c * (J.card : ℂ)) * T (bicharacterFourierSB μ he f) := by rw [hFourier]; ring
  refine ⟨h, fun hc hJ => ?_⟩
  have hvol : 0 < μ.real (A : Set R) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
  have hca : (c * (J.card : ℂ)) ≠ 0 := mul_ne_zero hc (Nat.cast_ne_zero.mpr hJ.card_pos.ne')
  change T χ = 0 ↔ T (bicharacterFourierSB μ he f) = 0
  constructor
  · intro hz
    rw [hz, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hca
  · intro hz
    rw [hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr hvol.ne')

end Langlands.HarmonicAnalysis.UnitConjugation
