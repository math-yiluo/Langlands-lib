import Langlands.BaseChange.CuspForm
import Langlands.BaseChange.EllipticOrbitalIntegral
import Langlands.BaseChange.TwistedCharacter

/-!
# Orbital integrals of cusp forms vanish off the elliptic set

Two statements on `GL_n` over a nonarchimedean local field `F` of characteristic zero, `0 < n`:

* `CuspFormOrbitalVanishingStatement`: a Schwartz–Bruhat function on `GL_n(F)` with vanishing
  constant terms (`HasVanishingConstantTerms`) has vanishing orbital integrals at every regular
  semisimple element that is not regular elliptic (`OrbitalIntegralsVanishOffElliptic`);
* `CuspFormSigmaOrbitalVanishingStatement`: for a field `E` that is a cyclic `F`-algebra with
  generator `σ`, a Schwartz–Bruhat function on `GL_n(E)` with vanishing constant terms has
  vanishing σ-orbital integrals at every σ-regular element that is not σ-elliptic
  (`SigmaOrbitalIntegralsVanishOffElliptic`).

Both follow from the descent formula for (σ-)orbital integrals along a parabolic subgroup
(Henniart–Lemaire 2011, II.4.5, formula (1)). Statements only; not proved here. See the paired
Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis

/-- For a nonarchimedean local field `F` of characteristic zero and `0 < n`: for every Haar
measure `μF` on `GL_n(F)` (Borel σ-algebra), every Schwartz–Bruhat function `f` on `GL_n(F)`
with vanishing constant terms along every proper standard block parabolic subgroup has vanishing
orbital integrals at every regular semisimple element that is not regular elliptic, for every
right Haar measure on the centralizer and every compatible quotient measure. -/
def CuspFormOrbitalVanishingStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (f : SchwartzBruhat (GeneralLinear n F)),
      HasVanishingConstantTerms (f : GeneralLinear n F → ℂ) →
        OrbitalIntegralsVanishOffElliptic μF (f : GeneralLinear n F → ℂ)

/-- For a nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic
`F`-algebra of group `⟨σ⟩` of order `l` with its module topology, and `0 < n`: for every Haar
measure `μE` on `GL_n(E)` (Borel σ-algebra), every Schwartz–Bruhat function `φ` on `GL_n(E)`
with vanishing constant terms along every proper standard block parabolic subgroup has vanishing
σ-orbital integrals at every σ-regular element that is not σ-elliptic, for every right Haar
measure on the σ-centralizer and every compatible quotient measure. -/
def CuspFormSigmaOrbitalVanishingStatement.{u, v} : Prop :=
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
    ∀ (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n E)),
      HasVanishingConstantTerms (φ : GeneralLinear n E → ℂ) →
        SigmaOrbitalIntegralsVanishOffElliptic σ l μE (φ : GeneralLinear n E → ℂ)

end Langlands.BaseChange
