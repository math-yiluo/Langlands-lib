import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Faithful flatness of dominant homomorphisms to reduced field groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A dominant homomorphism of finite-type group schemes over an algebraically
closed field is faithfully flat when its target is reduced. -/
def DominantGroupHomFlatStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType H.X.hom] [IsReduced H.X.left]
    (f : G ⟶ H) [IsDominant f.hom.hom.left],
      Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        QuasiCompact f.hom.hom.left

end Langlands.GroupScheme
