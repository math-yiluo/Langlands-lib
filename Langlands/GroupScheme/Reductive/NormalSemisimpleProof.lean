import Langlands.GroupScheme.Reductive.NormalSemisimpleReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof

/-! # Semisimplicity of smooth connected normal subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- A finite representative of the full centre of a smooth connected closed
normal subgroup of a semisimple group, over an arbitrary field. -/
def finiteCenterOfNormalSemisimpleUnconditional
    (hG : IsSemisimple G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : FiniteCenter H :=
  finiteCenterOfNormalSemisimple normalReductiveCenter hG i hi hn

/-- Every smooth connected closed normal subgroup of a semisimple group over
an arbitrary field is semisimple. -/
theorem IsSemisimple.of_normalSubgroup
    (hG : IsSemisimple G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : IsSemisimple H :=
  ⟨hG.isConnectedReductive.of_normalSubgroup i hi hn,
    (finiteCenterOfNormalSemisimpleUnconditional hG i hi hn).hasFiniteCenter⟩

end Langlands.GroupScheme
