import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Equivariant smooth additive quotients of smooth connected unipotent groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `k` be algebraically closed, `U` a nontrivial smooth connected affine unipotent
group of finite type over `k`, and let a diagonalizable group `D(Λ)` act on `U` by group
automorphisms. Then there are a character `χ` of `D(Λ)` and a smooth surjective
homomorphism `f : U ⟶ 𝔾ₐ` which is equivariant when `D(Λ)` acts on `𝔾ₐ` through `χ`.
The acting group need not be smooth or connected, and `Λ` is arbitrary. -/
def DiagonalizableUnipotentAdditiveQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (Λ : Type u) [AddCommGroup Λ]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom],
    Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
    SubgroupFunctor.range (𝟙 U) ≠ ⊥ →
    ∀ a : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp U,
      ∃ (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
        (f : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1),
        Smooth f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
        ∀ (T : Over (Spec (CommRingCat.of k)))
          (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ U.X),
          a.act d x ≫ f.hom.hom =
            (VectorGroup.weightAction (n := 1) χ).act d (x ≫ f.hom.hom)

end Langlands.GroupScheme
