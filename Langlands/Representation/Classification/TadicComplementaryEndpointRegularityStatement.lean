import Langlands.Representation.Classification.TadicComplementarySeriesStatement
import Langlands.Representation.Character.Basic
import Langlands.Group.GL.CompactOpen
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Regularity of the actual complementary family

A derived auxiliary target for the endpoint argument: admissibility, finite
length, and continuity of the actual distribution character.
-/

namespace Langlands.Classification

open GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

/-- The regularity facts needed to apply a finite-length character-limit
argument to Tadic's actual complementary family. -/
def ComplementaryEndpointRegularity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ {n : ℕ} (hn : 0 < n)
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    letI := T.generalLinearTopologicalGroup (2 * n)
    letI := T.generalLinearT2Space (2 * n)
    letI := T.generalLinearLocallyCompactSpace (2 * n)
    letI := T.generalLinearNonarchimedean (2 * n)
    letI : MeasurableSpace (GeneralLinear (2 * n) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (2 * n) F.Carrier) := ⟨rfl⟩
    IsAdmissible A.representation →
      (∀ s : ℝ, IsAdmissible (complementaryProduct F T hn A s).representation) ∧
      (A.IsIrreducible → ∀ s : ℝ,
        (complementaryProduct F T hn A s).HasFiniteLength) ∧
      (∀ (hπ : ∀ s : ℝ,
          IsAdmissible (complementaryProduct F T hn A s).representation)
        (μ : Measure (GeneralLinear (2 * n) F.Carrier))
        [IsFiniteMeasureOnCompacts μ] [Measure.IsMulLeftInvariant μ]
        (f : SchwartzBruhat (GeneralLinear (2 * n) F.Carrier)),
        Continuous (fun s : ℝ => Character.distribution μ
          (complementaryProduct F T hn A s).representation (hπ s) f))

end Langlands.Classification
