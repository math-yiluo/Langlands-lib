import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.Finiteness

/-! # Sections of trigonalizable groups with smooth unipotent part

Milne 16.27 with the hypothesis that the unipotent part is smooth (SGA 3 XVII 5.1.1 ii) b)).
This replaces `TrigonalizableSectionConjugacyStatement`, which is false in characteristic `p`. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.27, corrected by the hypothesis `Smooth U.X.hom` of SGA 3 XVII
5.1.1 ii) b). Let `G` be an affine algebraic group over an algebraically closed field `k` with a
smooth normal unipotent closed subgroup `i : U ⟶ G` and an fppf quotient `q : G ⟶ D(Λ)` by it
onto a diagonalizable group. (a) Any two homomorphic sections `s₁, s₂` of `q` are conjugate by a
rational point `u` of `U`: `s₂ = s₁ ≫ inn(u)`. (b) A closed diagonalizable subgroup of `G` is
maximal among closed diagonalizable subgroups if and only if its range is the range of a section
of `q`. Without the smoothness of `U` both parts fail in characteristic `p`; smoothness of `U` is
not necessary for (a), which also holds when `D(Λ)` is smooth (not stated here). -/
def TrigonalizableSectionConjugacySmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G)
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    IsClosedSubgroup i → Smooth U.X.hom → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
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
