import Langlands.Global.AdelicNormOneDecomposition
import Langlands.GroupScheme.Rational.CharactersStatement

/-! # Unconditional positive and norm-one adelic decomposition target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

/-- Multiplication through the actual positive-point map is a topological
group equivalence. The equivalence and its exact value are conclusions. -/
def HasPositiveNormOneDecomposition
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G) : Prop :=
  ∃ E : intrinsicSubgroup F T × normOneSubgroup F G ≃ₜ* AdelicGroupPoints F G,
    ∀ p, E p = positivePointMap F G T i p.1 * p.2

/-- Every connected reductive number-field group admits an actual split
component whose intrinsic positive points give the norm-one direct product.
No splitting, character-restriction or decomposition premise is supplied. -/
def AdelicPositiveDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsSplitComponent i ∧ HasPositiveNormOneDecomposition F G T i

end Langlands.Global.PositiveRealTorus
