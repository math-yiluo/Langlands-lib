import Langlands.HarmonicAnalysis.Distribution.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction

/-!
# Anti-invariant distributions supported on finitely many orbits vanish

The orbit-by-orbit reduction of Bernstein–Zelevinsky (1976), Theorem 6.9 and
Theorem 6.10, for a closed invariant set consisting of finitely many orbits.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uX

/-- Let a sigma-compact, locally compact nonarchimedean group `G` act
continuously on a Hausdorff, locally compact, totally disconnected space `X`.
Let `Z ⊆ X` be closed and equal to the union of the orbits of a finite set, and
let `σ` be a homeomorphism of `X` such that `σ z` and `σ⁻¹ z` lie in the orbit
of `z` for every `z ∈ Z`. Then every `G`-invariant distribution `D` on `X`
supported in `Z` with `σ_* D = -D` vanishes. -/
def FiniteOrbitAntiInvariantVanishingStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
      [LocallyCompactSpace G] [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
    (σ : X ≃ₜ X) (Z : Set X) (s : Finset X),
    IsClosed Z → Z = ⋃ x ∈ s, MulAction.orbit G x →
    (∀ z ∈ Z, σ z ∈ MulAction.orbit G z ∧ σ.symm z ∈ MulAction.orbit G z) →
    ∀ D : Distribution X,
      (∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0) →
      (∀ g : G, pushforward (Homeomorph.smul g) D = D) →
      pushforward σ D = -D → D = 0

end Langlands.HarmonicAnalysis.Distribution
