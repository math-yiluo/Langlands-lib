import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.Finiteness

/-! # Extensions of a smooth connected unipotent group by a diagonalizable group (Milne 16.28) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.28: let `e → D → G → U → e` be an exact sequence of affine
algebraic groups over a perfect field `k` (`i : D ⟶ G` a closed subgroup and `q : G ⟶ U` an fppf
quotient by it), with `D` diagonalizable and `U` smooth, connected and unipotent. Then `q` has
exactly one homomorphic section `s : U ⟶ G`, and for it `G ≃ D × U`: the points of `D` and of
`s(U)` commute and multiplication `D × U → G` is an isomorphism. -/
def PerfectDiagonalizableUnipotentExtensionSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (D U : GroupScheme (Spec (CommRingCat.of k))) (i : D ⟶ G) (q : G ⟶ U),
    IsClosedSubgroup i → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
    (∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (D ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)) →
    Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      (∃! s : U ⟶ G, s ≫ q = 𝟙 U) ∧
        ∀ s : U ⟶ G, s ≫ q = 𝟙 U →
          (∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ D.X) (y : T ⟶ U.X),
            (x ≫ i.hom.hom) * (y ≫ s.hom.hom) = (y ≫ s.hom.hom) * (x ≫ i.hom.hom)) ∧
          IsIso (subgroupMultiplication i s)

end Langlands.GroupScheme
