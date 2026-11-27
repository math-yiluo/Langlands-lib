import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Rational.LeviSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The weights of a split component inside a relative root datum

For a rational Levi subgroup `M` of a connected reductive group `G` with split component `A`,
the composite `A ⟶ G` factors through a homomorphism `T ⟶ G` from a split torus `T`. The real
cocharacters of `A` map injectively onto the common kernel of the relative roots of `T` vanishing
on them, and every relative root has an integral coroot whose reflection permutes the relative
roots and preserves the dimensions of their weight spaces in `Lie G`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RealTorusSpace

/-- **Weights of a split component inside a root datum.** For a rational Levi subgroup `M` of a
connected reductive group `G` over a field `F` with split component `A`, there is a homomorphism
`t : T ⟶ G` from a split torus `T` through which `A ⟶ G` factors, such that the real
cocharacters of `A` map injectively onto the common kernel of the relative roots of `t`
vanishing on them, and such that every relative root of `t` has an integral coroot whose
reflection permutes the relative roots and preserves the dimensions of their weight spaces. -/
def LeviSplitComponentRootDatumStatement : Prop :=
  ∀ (F : Type u) [Field F] (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of F))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of F))) (a : A.toGrp ⟶ M), IsSplitComponent a →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (t : T.toGrp ⟶ G) (g : A ⟶ T),
          IsSplitTorus T.toGrp ∧ CommGroupScheme.groupHom g ≫ t = a ≫ l ≫ p ∧
          Function.Injective (cocharacterMapReal g) ∧
          LinearMap.range (cocharacterMapReal g) =
            rootAnnihilator T {γ | γ ∈ relativeRoots t ∧
              ∀ x : V A, eval T γ (cocharacterMapReal g x) = 0} ∧
          ∀ γ ∈ relativeRoots t, ∃ γv : cocharacterLattice T, latticePairing T γ γv = 2 ∧
            ∀ δ ∈ relativeRoots t, δ - latticePairing T δ γv • γ ∈ relativeRoots t ∧
              Module.finrank F (weightSpace t (δ - latticePairing T δ γv • γ)) =
                Module.finrank F (weightSpace t δ)

end Langlands.GroupScheme
