import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.PseudoCoefficient
import Langlands.BaseChange.TwistedCharacter

/-!
# σ-discrete series are detected by test functions with σ-elliptic orbital integrals

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, every σ-discrete series representation `τ` of
`GL_{r+1}(E)`, with an isomorphism `A` of `τ` onto `τ^σ` and a Haar measure `μ`, has a
Schwartz–Bruhat test function `φ` whose σ-orbital integrals vanish at every σ-regular element
that is not σ-elliptic and whose twisted trace `tr(τ(φ) ∘ A)` is nonzero. A twisted
pseudo-coefficient of `(τ, A)` is such a function (Henniart–Lemaire 2011, II.5.13, Proposition,
and II.5.14, Proposition 2 (2), printed pp. 113–115; Arthur–Clozel 1989, Chapter 1,
Corollary 2.10 and Lemma 2.12 (ii), printed pp. 18–19). Statement only; not proved here. See
the paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `r : ℕ`: for every
σ-discrete series representation `τ` of `GL_{r+1}(E)` on `W : Type uW` (admissible), every
isomorphism `A` of `τ` onto `τ^σ` and every Haar measure `μ` on `GL_{r+1}(E)` (Borel
σ-algebra), some Schwartz–Bruhat function `φ` has σ-orbital integrals vanishing at every
σ-regular element that is not σ-elliptic (for every right Haar measure on its σ-centralizer and
every compatible quotient measure) and satisfies `tr(τ(φ) ∘ A) ≠ 0` (Henniart–Lemaire 2011,
II.5.13, Proposition, and II.5.14, Proposition 2 (2); Arthur–Clozel 1989, Chapter 1,
Corollary 2.10 and Lemma 2.12 (ii)). -/
def SigmaDiscreteEllipticOrbitalTestStatement.{u, v, uW} : Prop :=
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
        ∃ φ : SchwartzBruhat (GeneralLinear (r + 1) E),
          SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ ∧
            twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0

end Langlands.BaseChange
