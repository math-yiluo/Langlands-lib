import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Classification.Supercuspidal
import Mathlib.RepresentationTheory.Irreducible

/-!
# Matching cusp forms for a σ-stable supercuspidal representation

The statement that, for a cyclic field extension `E/F` of nonarchimedean local fields of
characteristic zero with generator `σ`, every σ-stable irreducible supercuspidal representation
`τ` of `GL_n(E)` with an isomorphism `A` of `τ` onto `τ^σ` admits a pair of concordant cusp forms
`φ` on `GL_n(E)` and `f` on `GL_n(F)` with `tr(τ(φ) ∘ A) ≠ 0`. This is the local input at the
auxiliary place in the twisted simple trace formula argument (Henniart–Lemaire 2011, II.6.3–6.4;
Arthur–Clozel 1989, Chapter 1, Lemma 2.12). Statement only; not proved here. See the paired
Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: for every
irreducible supercuspidal representation `τ` of `GL_n(E)` on `W : Type uW`, every isomorphism `A`
of `τ` onto `τ^σ` and all Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)` (Borel
σ-algebras), there are Schwartz–Bruhat functions `φ` on `GL_n(E)` and `f` on `GL_n(F)`, both with
vanishing constant terms along every proper standard parabolic subgroup, that are concordant
(HL I.2.5) and satisfy `tr(τ(φ) ∘ A) ≠ 0`. -/
def TwistedSupercuspidalCuspFormMatchingStatement.{u, v, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W) (hτ : GeneralLinear.IsSupercuspidal τ),
      τ.IsIrreducible →
      ∀ (A : SigmaIntertwiner σ n τ)
        (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
        (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
        ∃ (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
          HasVanishingConstantTerms (φ : GeneralLinear n E → ℂ) ∧
            HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) ∧
            AreConcordant σ l μF μE φ f ∧
            twistedDistribution μE τ hτ.1 A.toLinearMap φ ≠ 0

end Langlands.BaseChange
