import Mathlib.Algebra.LinearRecurrence
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Group.Defs

/-!
# Uniform recurrences and compact-set growth along translation orbits

A derived internal proposition target for continuous complex functions on a
topological group whose left translates span a finite-dimensional space, the
finite functions of Jacquet--Piatetski-Shapiro--Shalika (1979), printed
page 181. It is an interface for the valuation-shell recurrence route to
JPSS (1983), printed page 392, display (6). No proof is given here.
-/

namespace Langlands.HarmonicAnalysis

universe uG

/-- For a continuous `η : G → ℂ` with finite-dimensional span of left
translates `a ↦ η (b * a)` and any `t : G`, one linear recurrence `E` and one
growth base `B ≥ 1` serve every orbit sequence `n ↦ η (t ^ (n + k) * a)`, and
on each compact set `η (t ^ n * u)` is bounded by `C * B ^ |n|`. -/
def FiniteTranslationOrbitStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (η : G → ℂ), Continuous η →
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : G => fun a : G => η (b * a))) →
      ∀ t : G, ∃ (E : LinearRecurrence ℂ) (B : ℝ), 1 ≤ B ∧
        (∀ (k : ℤ) (a : G),
          E.IsSolution (fun n : ℕ => η (t ^ ((n : ℤ) + k) * a))) ∧
        ∀ K : Set G, IsCompact K → ∃ C : ℝ, 0 < C ∧
          ∀ n : ℤ, ∀ u ∈ K, ‖η (t ^ n * u)‖ ≤ C * B ^ n.natAbs

end Langlands.HarmonicAnalysis
