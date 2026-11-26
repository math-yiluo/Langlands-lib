import Langlands.BaseChange.EllipticSupport
import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Character.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! # Separation of essentially square-integrable traces on the regular elliptic set -/

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory
open scoped BigOperators

/-- An irreducible essentially square-integrable representation whose character distribution
lies in the span of a finite family of such distributions on regular elliptic tests is
equivalent to a member of that family. -/
def EllipticDiscreteTraceSeparationStatement.{u, uI, uV, uW} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ), 0 < n →
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
    ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
      (I : Type uI) [Fintype I] (V : I → Type uV) [∀ i, AddCommGroup (V i)]
      [∀ i, Module ℂ (V i)] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : (i : I) → Representation ℂ (GeneralLinear n F) (V i))
      (π : Representation ℂ (GeneralLinear n F) W)
      (hρ : ∀ i, IsAdmissible (ρ i)) (hπ : IsAdmissible π),
      (∀ i, (ρ i).IsIrreducible) → π.IsIrreducible →
      (∀ i, IsEssentiallySquareIntegrable (ρ i)) → IsEssentiallySquareIntegrable π →
      ∀ a : I → ℂ,
        (∀ f : SchwartzBruhat (GeneralLinear n F), IsEllipticSupported f →
          Character.distribution μ π hπ f =
            ∑ i, a i * Character.distribution μ (ρ i) (hρ i) f) →
        ∃ i, Nonempty (π.Equiv (ρ i))

end Langlands.BaseChange
