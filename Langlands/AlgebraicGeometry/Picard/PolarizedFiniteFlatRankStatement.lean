import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Native rank of a polarized finite flat endomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A finite flat endomorphism of a smooth proper geometrically connected
scheme of relative dimension `g` over an algebraically closed field has native
rank `q ^ g` when it pulls an ample line bundle back to its `q`-th tensor power.
This is a statement target. -/
def PolarizedFiniteFlatRankStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (X : Over (Spec (CommRingCat.of K))) (g : ℕ),
    SmoothOfRelativeDimension g X.hom →
      IsProper X.hom → GeometricallyConnected X.hom →
        ∀ (f : X ⟶ X), IsFinite f.left → Flat f.left →
          ∀ (L : LineBundle X.left), L.IsAmple →
            ∀ (q : ℕ), 0 < q →
              Nonempty
                ((_root_.AlgebraicGeometry.Scheme.Modules.pullback f.left).obj L.obj ≅
                  Langlands.Scheme.Modules.tensorPow L.obj q) →
                ∀ (x : X.left), f.left.finrank x = q ^ g

end Langlands.AlgebraicGeometry.Picard
