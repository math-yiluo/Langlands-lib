import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Mathlib.RepresentationTheory.Irreducible

/-!
# Twisted traces of σ-stable supercuspidals are detected on the σ-elliptic set

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, the twisted distribution character
`φ ↦ tr(τ(φ) ∘ A)` of a σ-stable irreducible supercuspidal representation `τ` of `GL_n(E)`
(`0 < n`) is nonzero on some Schwartz–Bruhat function supported in the σ-elliptic set.
This is a local test-function consequence of Arthur–Clozel 1989, Chapter 1, Lemma 2.12(i)
and Proposition 2.2; see Henniart–Lemaire 2011, II.6.4 for the role of σ-elliptic support
in the simple twisted trace formula. Statement only; not proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: for every
irreducible supercuspidal representation `τ` of `GL_n(E)` on `W : Type uW`, every isomorphism `A`
of `τ` onto `τ^σ` and every Haar measure `μ` on `GL_n(E)` (Borel σ-algebra), some
Schwartz–Bruhat function `φ` supported in the σ-elliptic set has `tr(τ(φ) ∘ A) ≠ 0`. -/
def TwistedSupercuspidalEllipticNonvanishingStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        ∃ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaEllipticSupported σ l φ ∧
          twistedDistribution μ τ hτ.1 A.toLinearMap φ ≠ 0

end Langlands.BaseChange
