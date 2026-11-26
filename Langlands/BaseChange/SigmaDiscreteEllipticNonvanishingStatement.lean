import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# Twisted characters of σ-discrete series are detected on the σ-elliptic set

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, the twisted distribution character
`φ ↦ tr(τ(φ) ∘ A)` of a σ-discrete series representation `τ` of `GL_{r+1}(E)` is nonzero on
some Schwartz–Bruhat function supported in the σ-elliptic set. This generalizes the Library's
`TwistedSupercuspidalEllipticNonvanishingStatement` from supercuspidal to σ-discrete series.
It is the test-function form of Henniart–Lemaire 2011, II.5.14, Corollaire 2 (printed p. 117),
and Arthur–Clozel 1989, Chapter 1, Lemma 2.12 (i) (printed p. 19). Statement only; not proved
here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: for every
σ-discrete series representation `τ` of `GL_{r+1}(E)` on `W : Type uW` (admissible), every
isomorphism `A` of `τ` onto `τ^σ` and every Haar measure `μ` on `GL_{r+1}(E)` (Borel
σ-algebra), some Schwartz–Bruhat function `φ` supported in the σ-elliptic set has
`tr(τ(φ) ∘ A) ≠ 0` (Henniart–Lemaire 2011, II.5.14, Corollaire 2; Arthur–Clozel 1989,
Chapter 1, Lemma 2.12 (i)). -/
def SigmaDiscreteEllipticNonvanishingStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l r : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E (r + 1)
    haveI := generalLinear_locallyCompactSpace_of_finite F E (r + 1)
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E (r + 1)
    letI : MeasurableSpace (GeneralLinear (r + 1) E) := borel _
    haveI : BorelSpace (GeneralLinear (r + 1) E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear (r + 1) E) W) (hτ : IsAdmissible τ),
      IsSigmaDiscreteSeries σ (r + 1) τ →
      ∀ (A : SigmaIntertwiner σ (r + 1) τ) (μ : Measure (GeneralLinear (r + 1) E))
        [μ.IsHaarMeasure],
        ∃ φ : SchwartzBruhat (GeneralLinear (r + 1) E), IsSigmaEllipticSupported σ l ⇑φ ∧
          twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0

end Langlands.BaseChange
