import Langlands.HarmonicAnalysis.UnitConjugation.PairingHaar

/-! # Conjugation invariance under the additive Fourier transform -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory _root_.Topology
open Hecke.TestFunction (pullback pullback_apply)

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [T2Space A] [CompactOpenExhaustion A] [MeasurableSpace A] [BorelSpace A]
  (μ : Measure A) [μ.IsAddHaarMeasure] {e : A → A → ℂ} (he : IsSelfDualBicharacter e)

/-- If unit conjugation preserves both the bicharacter and Haar measure,
the Fourier transform of an invariant distribution is invariant. -/
def FourierConjugationStatement (D : Distribution A) : Prop :=
  (∀ u : Aˣ, MeasurePreserving (conjugationHomeomorph u) μ μ) →
  (∀ (u : Aˣ) (x y : A), e (conjugationHomeomorph u x) (conjugationHomeomorph u y) = e x y) →
  IsConjugationInvariant D → IsConjugationInvariant ((bicharacterFourierSB μ he).dualMap D)

omit [T2Space A] [CompactOpenExhaustion A] in
theorem fourierConjugation (D : Distribution A) : FourierConjugationStatement μ he D := by
  intro hμ heInv hD
  apply (isConjugationInvariant_iff _).mpr
  intro u g
  let a := conjugationHomeomorph u
  have hComm : bicharacterFourierSB μ he (pullback a g) = pullback a (bicharacterFourierSB μ he g) := by
    apply Hecke.TestFunction.ext
    intro x
    change (∫ y, e x y * g (a y) ∂μ) = ∫ y, e (a x) y * g y ∂μ
    have hPair (y : A) : e (a x) (a y) = e x y := heInv u x y
    calc
      _ = ∫ y, e (a x) (a y) * g (a y) ∂μ := by simp_rw [hPair]
      _ = _ := (hμ u).integral_comp a.toMeasurableEquiv.measurableEmbedding (fun y => e (a x) y * g y)
  change D (bicharacterFourierSB μ he (pullback a g)) = D (bicharacterFourierSB μ he g)
  rw [hComm]
  exact (isConjugationInvariant_iff D).mp hD u _

end Langlands.HarmonicAnalysis.UnitConjugation
