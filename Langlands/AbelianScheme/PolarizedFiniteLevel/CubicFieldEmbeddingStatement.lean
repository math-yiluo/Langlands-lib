import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicEvaluation
import Langlands.AlgebraicGeometry.LinearSystem.RelativeMorphism

/-! # The cubic Lefschetz embedding of an ordinary polarized datum over a field -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.LinearSystem

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- Lefschetz's theorem for the canonical cubic bundle of an actual ordinary
polarized datum over a field. The full cubic evaluation is an epimorphism,
so the complete linear system has no base points. The morphism to projective
space given by any basis of the global sections is a closed immersion.
This proposition is a statement, not a proof of it. -/
def CubicFieldEmbeddingStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ), 0 < d →
    ∀ a : Datum P (Spec (CommRingCat.of K)) g d n,
      Epi a.cubicEvaluationAdjoint ∧
        ∀ (m : ℕ) (b : Module.Basis (Fin (m + 1)) K
            ((relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj))
          (hb : ∀ x : a.abelian.X.left, ∃ i,
            x ∈ nonvanishingLocus a.cubicBundle.obj (b i)),
          IsClosedImmersion (relativeLinearSystemMap a.abelian.X.hom hb)

end Langlands.AbelianScheme.PolarizedFiniteLevel
