import Langlands.GroupScheme.Reductive.NormalSubgroup
import Langlands.GroupScheme.Reductive.NormalCenterDescent
import Langlands.GroupScheme.Reductive.FiniteCenterBaseChange

/-! # Normal semisimple subgroups under full-centre containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- Construct a finite representative of the full centre of a smooth connected
normal subgroup of a semisimple group, conditional on full-centre containment
for normal connected reductive subgroups. -/
def finiteCenterOfNormalSemisimple
    (hCenter : NormalReductiveCenterStatement.{u})
    (hG : IsSemisimple G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : FiniteCenter H := by
  let hH := hG.isConnectedReductive.of_normalSubgroup i hi hn
  let ZG := hG.hasFiniteCenter.choose
  let zG := hG.hasFiniteCenter.choose_spec.choose
  have hzG : IsSchemeTheoreticCenter zG :=
    hG.hasFiniteCenter.choose_spec.choose_spec.1
  have hfinG : IsFinite ZG.X.hom :=
    hG.hasFiniteCenter.choose_spec.choose_spec.2
  let hExistsH := schemeTheoreticCenterExistence k H hH
  let ZH := hExistsH.choose
  let zH := hExistsH.choose_spec.choose
  have hzH : IsSchemeTheoreticCenter zH := hExistsH.choose_spec.choose_spec
  let f := normalCenterMap hCenter hG.isConnectedReductive hH i hi hn zH hzH zG hzG
  have hf : IsClosedSubgroup f :=
    normalCenterMap_isClosedSubgroup hCenter hG.isConnectedReductive hH
      i hi hn zH hzH zG hzG
  letI : IsClosedImmersion f.hom.hom.left := hf
  letI : IsFinite ZG.X.hom := hfinG
  refine ⟨ZH, zH, hzH, ?_⟩
  rw [← f.hom.hom.w]
  infer_instance

/-- Smooth connected normal closed subgroups of semisimple groups are
semisimple, conditional on the normal full-centre containment proposition. -/
theorem IsSemisimple.of_normalSubgroup_of_normalReductiveCenterStatement
    (hCenter : NormalReductiveCenterStatement.{u})
    (hG : IsSemisimple G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) : IsSemisimple H :=
  ⟨hG.isConnectedReductive.of_normalSubgroup i hi hn,
    (finiteCenterOfNormalSemisimple hCenter hG i hi hn).hasFiniteCenter⟩

end Langlands.GroupScheme
