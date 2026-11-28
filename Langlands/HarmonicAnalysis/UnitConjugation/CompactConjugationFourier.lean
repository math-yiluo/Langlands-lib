import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar
import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicFourier

/-! # Fourier transform and compact conjugation averages -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory

universe u v

section Average

variable {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (C : Set Aˣ) (hC : IsCompact C)

private def compactConjugationKernel (f : SchwartzBruhat A) : SchwartzBruhat (A × C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let one : SchwartzBruhat C :=
    ⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩
  let T : A × C → A × C := fun p => ((conjugationHomeomorph p.2.val).symm p.1, p.2)
  let S : A × C → A × C := fun p => (conjugationHomeomorph p.2.val p.1, p.2)
  have hval : Continuous (fun p : A × C => ((p.2.val : Aˣ) : A)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)
  have hinv : Continuous (fun p : A × C => ((p.2.val⁻¹ : Aˣ) : A)) :=
    Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)
  have hT : Continuous T :=
    ((hinv.mul continuous_fst).mul hval).prodMk continuous_snd
  have hS : Continuous S :=
    ((hval.mul continuous_fst).mul hinv).prodMk continuous_snd
  exact (SchwartzBruhat.tensor f one).compLeftInverse T S hT hS fun p =>
    Prod.ext ((conjugationHomeomorph p.2.val).apply_symm_apply p.1) rfl

private theorem compactConjugationKernel_apply (f : SchwartzBruhat A) (x : A) (k : C) :
    compactConjugationKernel C hC f (x, k) = f ((conjugationHomeomorph k.val).symm x) :=
  mul_one _

variable [MeasurableSpace Aˣ] [BorelSpace Aˣ] (μC : Measure C) [IsFiniteMeasureOnCompacts μC]

/-- Average a test over inverse conjugations by the units of a compact set. -/
def compactConjugationAverage (f : SchwartzBruhat A) : SchwartzBruhat A :=
  (compactConjugationKernel C hC f).partialIntegral μC

theorem compactConjugationAverage_apply (f : SchwartzBruhat A) (x : A) :
    compactConjugationAverage C hC μC f x =
      ∫ k : C, f ((conjugationHomeomorph k.val).symm x) ∂μC := by
  unfold compactConjugationAverage
  simp only [SchwartzBruhat.partialIntegral_apply, compactConjugationKernel_apply]

end Average

section Fourier

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
  [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]

/-- Fourier transform commutes with pullback by fixed-unit conjugation for an invariant
pairing. -/
theorem pairingFourierSB_pullback_conjugation [IsTopologicalRing A]
    (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F A} (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) (g : Aˣ) (f : SchwartzBruhat A) :
    pairingFourierSB ψ hB.isSymm hB.nondegenerate μ
        (Hecke.TestFunction.pullback (conjugationHomeomorph g).symm f) =
      Hecke.TestFunction.pullback (conjugationHomeomorph g).symm
        (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f) := by
  ext y
  rw [Hecke.TestFunction.pullback_apply, pairingFourierSB_apply, pairingFourierSB_apply]
  let E := conjugationHomeomorph g
  let k : A → ℂ := fun x => ψ.complex (B y x) * f (E.symm x)
  change (∫ x, k x ∂μ.measure) = ∫ x, ψ.complex (B (E.symm y) x) * f x ∂μ.measure
  have hPres := pairingHaarPreservation B μ.measure hB g
  rw [← hPres.integral_comp E.toMeasurableEquiv.measurableEmbedding k]
  apply integral_congr_ae
  filter_upwards [] with x
  change k (E x) = ψ.complex (B (E.symm y) x) * f x
  have hBxy : B (E.symm y) x = B y (E x) := by
    have h := hB.conj_invariant g (E.symm y) x
    change B (E (E.symm y)) (E x) = _ at h
    rw [E.apply_symm_apply] at h
    exact h.symm
  simp only [k, E.symm_apply_apply, hBxy]

/-- The Fourier transform for an invariant pairing commutes with compact
conjugation averaging. -/
def CompactConjugationFourierStatement [MeasurableSpace Aˣ] [BorelSpace Aˣ] : Prop :=
  haveI := IsModuleTopology.isTopologicalRing F A
  haveI : T2Space A := t2Space_of_finiteDimensional F A
  ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) (C : Set Aˣ) (hC : IsCompact C) (μC : Measure C)
    [IsFiniteMeasureOnCompacts μC] (f : SchwartzBruhat A),
    pairingFourierSB ψ hB.isSymm hB.nondegenerate μ (compactConjugationAverage C hC μC f) =
      compactConjugationAverage C hC μC (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f)

theorem compactConjugationFourier [MeasurableSpace Aˣ] [BorelSpace Aˣ] :
    CompactConjugationFourierStatement (F := F) (A := A) := by
  have := IsModuleTopology.isTopologicalRing F A
  have : T2Space A := t2Space_of_finiteDimensional F A
  have : LocallyCompactSpace A := locallyCompactSpace_of_finiteDimensional F A
  have : SecondCountableTopology A := secondCountableTopology_of_finiteDimensional F A
  intro ψ B hB μ C hC μC _ f
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  ext y
  let φ := compactConjugationKernel C hC f
  let κ : A → ℂ := fun x => ψ.complex (B y x)
  have hκ : Continuous κ := ψ.continuous_complex.comp (continuous_of_linearMap' (B y))
  have hi : Integrable (fun p : A × C => κ p.1 * φ p) (μ.measure.prod μC) :=
    ((hκ.comp continuous_fst).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  rw [pairingFourierSB_apply, compactConjugationAverage_apply]
  change (∫ x, κ x * (∫ k : C, φ (x, k) ∂μC) ∂μ.measure) =
    ∫ k : C, pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f
      ((conjugationHomeomorph k.val).symm y) ∂μC
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with k
  have h := congrArg (fun t : SchwartzBruhat A => t y)
    (pairingFourierSB_pullback_conjugation ψ hB μ k.val f)
  rw [pairingFourierSB_apply, Hecke.TestFunction.pullback_apply] at h
  simp only [Hecke.TestFunction.pullback_apply] at h
  simp only [φ, κ, compactConjugationKernel_apply]
  exact h

/-- The averaged constant term of the ambient transform is the Levi transform
of the averaged constant term, with the normalized Levi Haar measure. -/
theorem idempotentParabolicAveragedFourier [CharZero F] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    (e : A) (he : IsIdempotentElem e) (ψ : UnitaryAdditiveCharacter F)
    {B : LinearMap.BilinForm F A} (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) (C : Set Aˣ) (hC : IsCompact C)
    (μC : Measure C) [IsFiniteMeasureOnCompacts μC]
    (ν : Measure (IdempotentCentralizer.offDiagonalCorner F e)) [ν.IsAddHaarMeasure] :
    haveI := IsModuleTopology.isTopologicalRing F A
    haveI : T2Space A := t2Space_of_finiteDimensional F A
    haveI : IsModuleTopology F (Subalgebra.centralizer F {e}) :=
      isModuleTopology_submodule (Subalgebra.centralizer F {e}).toSubmodule
    let hM := IdempotentCentralizer.invariantPairing_centralizer he hB
    ∃ μM : AdditiveHaarMeasure (Subalgebra.centralizer F {e}), ∀ f : SchwartzBruhat A,
      IdempotentCentralizer.parabolicConstantTerm F he ν
        (compactConjugationAverage C hC μC (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f)) =
        pairingFourierSB ψ hM.isSymm hM.nondegenerate μM
          (IdempotentCentralizer.parabolicConstantTerm F he ν (compactConjugationAverage C hC μC f)) := by
  have := IsModuleTopology.isTopologicalRing F A
  have : T2Space A := t2Space_of_finiteDimensional F A
  obtain ⟨μM, h⟩ := IdempotentCentralizer.idempotentParabolicFourier F e he ψ B hB μ ν
  refine ⟨μM, fun f => ?_⟩
  rw [← compactConjugationFourier ψ B hB μ C hC μC f]
  exact h (compactConjugationAverage C hC μC f)

end Fourier

end Langlands.HarmonicAnalysis.UnitConjugation
