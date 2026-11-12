import Langlands.Sheaf.Renard.ModuleProjectorComparison

/-!
# Statement: the original-module comparison is an isomorphism

Renard (9 July 2026), II.2.5, end of the proof of the Theorem, printed p.40 / PDF p.46.
-/

namespace Langlands.Sheaf.Renard.ModuleProjectorComparison

open CategoryTheory

/-- Renard II.2.5: for every nondegenerate test module `M` on a t.d. space, the comparison
`M ⟶ Γc(P M)`, `m ↦ (χ_U · m)_U`, is an isomorphism. -/
def ModuleComparisonIsIso : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (hX : Langlands.Topology.IsLocallyProfinite X)
    (M : Langlands.Algebra.NondegenerateModuleCat.{0, 0}
      (Langlands.HarmonicAnalysis.PointwiseTestAlgebra.Carrier X)),
    IsIso (moduleComparison hX M)

end Langlands.Sheaf.Renard.ModuleProjectorComparison
