import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Sections and maximal diagonalizable subgroups of trigonalizable groups (Milne 16.27) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.27: let `G` be an affine algebraic group over an algebraically closed
field `k` with a normal unipotent closed subgroup `i : U ⟶ G` and an fppf quotient
`q : G ⟶ D(Λ)` by it onto a diagonalizable group (so `G` is trigonalizable and `U = G_u`).
(a) Any two homomorphic sections `s₁, s₂` of `q` are conjugate by a rational point `u` of `U`:
`s₂ = s₁ ≫ inn(u)`. (b) A closed diagonalizable subgroup of `G` is maximal among closed
diagonalizable subgroups if and only if its range is the range of a section of `q`. -/
def TrigonalizableSectionConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q →
      let IsDiag : GroupScheme (Spec (CommRingCat.of k)) → Prop := fun S =>
        ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
          Nonempty (S ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp)
      (∀ s₁ s₂ : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G,
        s₁ ≫ q = 𝟙 _ → s₂ ≫ q = 𝟙 _ →
          ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
            s₂ = s₁ ≫ (G.innerIso (u ≫ i.hom.hom)).hom) ∧
      ∀ (S : GroupScheme (Spec (CommRingCat.of k))) (j : S ⟶ G),
        IsClosedSubgroup j → IsDiag S →
          ((∀ (S' : GroupScheme (Spec (CommRingCat.of k))) (j' : S' ⟶ G),
              IsClosedSubgroup j' → IsDiag S' →
                SubgroupFunctor.range j ≤ SubgroupFunctor.range j' →
                  SubgroupFunctor.range j = SubgroupFunctor.range j') ↔
            ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G,
              s ≫ q = 𝟙 _ ∧ SubgroupFunctor.range j = SubgroupFunctor.range s)

end Langlands.GroupScheme
