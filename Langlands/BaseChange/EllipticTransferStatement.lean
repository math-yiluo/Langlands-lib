import Langlands.BaseChange.EllipticSupport
import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Statement: transfer of test functions supported in the elliptic set

For a nonarchimedean local field `F` of characteristic zero and a cyclic `F`-algebra `E` of
group `⟨σ⟩` of order `l`: every σ-elliptic-supported test function on `GL_n(E)` has a concordant
elliptic-supported test function on `GL_n(F)`, and every elliptic-supported test function on
`GL_n(F)` whose orbital integrals vanish off the norms has a concordant σ-elliptic-supported
test function on `GL_n(E)` (the regular transfer of Henniart–Lemaire 2011, I.2.5, Proposition,
printed p. 18, restricted to the elliptic set, as used in II.6.3, II.6.4 and II.6.10). The
statement is not proved here. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

universe u v

/-- Elliptic transfer (Henniart–Lemaire, I.2.5, Proposition, restricted to the elliptic set;
II.6.3, II.6.4, II.6.10): for all Haar measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)`,
(1) every test function `φ` on `GL_n(E)` supported in the σ-elliptic set is concordant with a
test function `f` on `GL_n(F)` supported in the regular elliptic set; (2) every test function
`f` on `GL_n(F)` supported in the regular elliptic set whose orbital integrals vanish at the
regular non-norms is concordant with a test function `φ` on `GL_n(E)` supported in the
σ-elliptic set. -/
def EllipticTransferStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    IsCyclicAlgebra σ l →
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    ∀ (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n E)),
      μF.IsHaarMeasure → μE.IsHaarMeasure →
      (∀ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaEllipticSupported σ l (φ : _ → ℂ) →
        ∃ f : SchwartzBruhat (GeneralLinear n F), IsEllipticSupported (f : _ → ℂ) ∧
          AreConcordant σ l μF μE (φ : _ → ℂ) (f : _ → ℂ)) ∧
      (∀ f : SchwartzBruhat (GeneralLinear n F), IsEllipticSupported (f : _ → ℂ) →
        VanishesOffNorms σ l μF (f : _ → ℂ) →
        ∃ φ : SchwartzBruhat (GeneralLinear n E), IsSigmaEllipticSupported σ l (φ : _ → ℂ) ∧
          AreConcordant σ l μF μE (φ : _ → ℂ) (f : _ → ℂ))

end Langlands.BaseChange
