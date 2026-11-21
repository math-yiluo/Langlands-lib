import Langlands.BaseChange.TwistedCharacter
import Mathlib.RepresentationTheory.Irreducible

/-!
# Twisted traces are detected by σ-regularly supported test functions

The statement that the twisted distribution character `φ ↦ tr(τ(φ) ∘ A)` of an irreducible
admissible representation `τ` of `GL_n(E)`, for a cyclic algebra `E` over a nonarchimedean local
field `F` of characteristic zero and an isomorphism `A` of `τ` onto `τ^σ`, is nonzero on some
Schwartz–Bruhat function supported in the σ-regular set. It is a consequence of the density
theorem for irreducible admissible representations and of the local integrability of twisted
characters, which in characteristic zero is Clozel 1987 (Arthur–Clozel 1989, Chapter 1,
Proposition 2.2; Henniart–Lemaire 2011, II.2.8 for the reduction to a field). Statement only; not
proved here. See the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a cyclic `F`-algebra `E` of group
`⟨σ⟩` of order `l` with its module topology, and `n : ℕ`: for every irreducible admissible
representation `τ` of `GL_n(E)` on a complex vector space `W : Type uW`, every isomorphism `A` of
`τ` onto `τ^σ` and every Haar measure `μ` on `GL_n(E)` (Borel σ-algebra), some Schwartz–Bruhat
function `φ` supported in the σ-regular set has `tr(τ(φ) ∘ A) ≠ 0`. -/
def TwistedTraceRegularNonvanishingStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) →
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ), τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ) (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        ∃ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaRegularSupported σ l φ ∧
          twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0

end Langlands.BaseChange
