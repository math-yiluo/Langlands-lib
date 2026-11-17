import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle
import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Effective polarized scheme descent for a cartesian étale relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- A smooth proper scheme with ample coherent transport along a cartesian
étale descent relation has an invariant scheme descent, cartesian over the
original affine base cover. -/
def PolarizedEtaleRelationEffectivityStatement : Prop :=
  ∀ (S U : Scheme.{u}), IsAffine S → IsAffine U →
    ∀ (p : U ⟶ S), Etale p → Surjective p →
      ∀ (E : EtaleEquivalenceRelation.{u}) (f : E.U ⟶ U),
        Smooth f → IsProper f →
          IsPullback E.t (E.s ≫ f) (f ≫ p) p →
            ∀ (B : EquivariantLineBundle E), B.bundle.IsAmple →
              ∃ (N : Over S) (q : E.U ⟶ N.left),
                IsPullback q f N.hom p ∧ E.t ≫ q = E.s ≫ q

end Langlands.AlgebraicGeometry.Picard
