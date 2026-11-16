import Mathlib.RingTheory.Etale.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.WeilRestriction

/-! # Statement: the adjoint torus of a relative Borel is a finite étale Weil torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A supplied maximal torus in a relative Borel has an induced adjoint torus.
The target is the actual supplied full fppf quotient by the inverse image of
its ambient group's full centre. The finite étale coefficient algebra may be
the zero ring, as needed when the root system is empty. -/
def RelativeBorelAdjointTorusWeilPresentationStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G B : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G),
    IsReductive G → IsRelativeBorelSubgroup i →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of R))) (t : T.toGrp ⟶ B),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup (t ≫ i) →
      IsFibrewiseMaximalTorus (t ≫ i) →
      ∀ (D : GroupScheme (Spec (CommRingCat.of R))) (q : T.toGrp ⟶ D),
        RelativeRoot.IsFppfQuotient ((center G).comap (t ≫ i)) q →
        ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E)
          (_ : Module.Finite R E) (_ : Module.Projective R E),
          Algebra.Etale R E ∧
            Nonempty (D ≅ WeilGm.groupScheme (CommRingCat.of R) E)

end Langlands.GroupScheme
