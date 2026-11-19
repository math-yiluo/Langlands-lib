import Langlands.BaseChange.PseudoCoefficient
import Langlands.JacquetLanglands.EssentiallySquareIntegrable

/-!
# Existence of pseudo-coefficients of square-integrable representations of `GL_n(F)`

Kazhdan (1986), Theorem K(a), in the fixed central character form of Henniart–Lemaire (2011),
II.5.13, Proposition, for `E = F` and `σ = 1`. Stated as a proposition, not proved here. See
the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis

/-- Existence of pseudo-coefficients (Kazhdan 1986, Theorem K(a); with a fixed central
character as in Henniart–Lemaire, II.5.13, Proposition, for `E = F`, `σ = 1`). Let `F` be a
nonarchimedean local field of characteristic zero, and give `GL_n(F)` its Borel σ-algebra. For
every irreducible admissible square-integrable representation `π` of `GL_n(F)` on a complex
vector space `V`, every character `χ` of the centre that is the central character of `π`, and
every Haar measure `μ` on `GL_n(F)`, there is `f ∈ C^∞_c(GL_n(F))` that is a pseudo-coefficient
of `π` with central character `χ`. -/
def PseudoCoefficientExistenceStatement.{u, uV} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GeneralLinear n F) V)
      (hπ : IsAdmissible π), π.IsIrreducible → JacquetLanglands.IsSquareIntegrable π →
      ∀ χ : Subgroup.center (GeneralLinear n F) →* ℂˣ, HasCentralCharacterRep π χ →
      ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure],
        ∃ f : SchwartzBruhat (GeneralLinear n F), IsPseudoCoefficient μ χ π hπ f

end Langlands.BaseChange
