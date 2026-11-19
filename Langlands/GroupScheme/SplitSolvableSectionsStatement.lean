import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.Split

/-! # Sections of the canonical extension of a split solvable group (Milne 16.54) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.54: let `G` be a split solvable group over a field `k`, with
its canonical extension `e → G_u → G → D → e` given by a normal unipotent closed subgroup
`i : U ⟶ G` and an fppf quotient `q : G ⟶ D` by it onto a group of multiplicative type. Then
`q` has a homomorphic section; any two sections are conjugate by a rational point of `U`; and
a closed split torus of `G` is maximal among closed split tori if and only if its range is the
range of a section of `q`. -/
def SplitSolvableExtensionSectionsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSplitSolvableGroupScheme G →
    ∀ (U D : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ D),
      IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q → IsMultiplicativeType D →
      (∃ s : D ⟶ G, s ≫ q = 𝟙 D) ∧
      (∀ s₁ s₂ : D ⟶ G, s₁ ≫ q = 𝟙 D → s₂ ≫ q = 𝟙 D →
        ∃ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
          s₂ = s₁ ≫ (G.innerIso (u ≫ i.hom.hom)).hom) ∧
      ∀ (S : GroupScheme (Spec (CommRingCat.of k))) (j : S ⟶ G),
        IsClosedSubgroup j → IsSplitTorus S →
          ((∀ (S' : GroupScheme (Spec (CommRingCat.of k))) (j' : S' ⟶ G),
              IsClosedSubgroup j' → IsSplitTorus S' →
                SubgroupFunctor.range j ≤ SubgroupFunctor.range j' →
                  SubgroupFunctor.range j = SubgroupFunctor.range j') ↔
            ∃ s : D ⟶ G, s ≫ q = 𝟙 D ∧ SubgroupFunctor.range j = SubgroupFunctor.range s)

end Langlands.GroupScheme
