import Langlands.GroupScheme.ProjectiveDualLineChart
import Langlands.GroupScheme.Torus.Split
import Mathlib.Topology.KrullDimension

/-! # Statement: the projective linear torus fixed-point dimension bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **The projective linear torus fixed-point bound** (Milne, Proposition
20.11). A nonempty reduced finite-type scheme with an actual equivariant closed
immersion into the projectivization of a finite-dimensional torus representation
has at least `d + 1` distinct all-test fixed rational points whenever its
topological Krull dimension is at least `d`. -/
def ProjectiveTorusFixedPointDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus T.toGrp →
    ∀ (n : ℕ) (X : Over (Spec (CommRingCat.of k)))
      [IsReduced X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [Nonempty X.left]
      (a : SchemeAction T.toGrp X)
      (ρ : MatrixRepresentation T.toGrp (Fin (n + 1)))
      (φ : X ⟶ ProjectiveOrbit.ambient n (CommRingCat.of k)),
      IsClosedImmersion φ.left → ProjectiveOrbit.IsMatrixEquivariant a ρ φ →
      ∀ d : ℕ, (d : WithBot ℕ∞) ≤ topologicalKrullDim X.left →
        ∃ x : Fin (d + 1) → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X),
          Function.Injective x ∧ ∀ j, a.IsFixed (x j)

end Langlands.GroupScheme
