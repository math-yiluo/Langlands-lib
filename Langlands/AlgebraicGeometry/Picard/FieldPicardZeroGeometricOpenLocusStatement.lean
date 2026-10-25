import Langlands.AlgebraicGeometry.Picard.FieldPicardZeroOpenLocusStatement

/-! # A geometric-point open locus in a universal field Picard parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- An ambient universal rigidified family over a field has an open locus that
classifies its actual geometric-point pullbacks. -/
def FieldPicardZeroGeometricOpenLocusStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (P : Over (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (L : RigidifiedFamily A P),
    LocallyOfFiniteType P.hom →
      RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
        ∃ U : P.left.Opens,
          ∀ (K : Type u) [Field K] [IsAlgClosed K]
            (s : Spec (CommRingCat.of K) ⟶ P.left),
            IsPicardZeroFamily A
              ((RigidifiedLineBundle.relativePullback A.X.hom
                (unitSection A) (unitSection_comp A)
                (Over.homMk s rfl : Over.mk (s ≫ P.hom) ⟶ P)).obj L) ↔
              Set.range s ⊆ (U : Set P.left)

end Langlands.AbelianScheme
