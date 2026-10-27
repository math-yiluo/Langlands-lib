import Langlands.AlgebraicGeometry.Picard.FieldPicardIdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Geometric-point families and the origin component of a universal field Picard parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- For a universal rigidified family over a field, an actual geometric point of the parameter
scheme pulls the family back to a geometrically Picard-zero family exactly when its image lies
in the connected component of the origin point. -/
def FieldPicardZeroGeometricComponentComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    LocallyOfFiniteType P.hom →
      ∀ hL : RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L,
        ∀ (K : Type u) [Field K] [IsAlgClosed K]
          (s : Spec (CommRingCat.of K) ⟶ P.left),
          IsPicardZeroFamily A
            ((RigidifiedLineBundle.relativePullback A.X.hom
              (unitSection A) (unitSection_comp A)
              (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
            Set.range s ⊆ connectedComponent (fullPicardOriginPoint k A L hL)

end Langlands.AbelianScheme
