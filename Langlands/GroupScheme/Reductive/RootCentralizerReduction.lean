import Langlands.GroupScheme.Reductive.RootGenerationStatement
import Langlands.GroupScheme.Reductive.NormalRootDichotomyStatement
import Langlands.GroupScheme.Reductive.NormalCentralizer
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Closed generation by a normal subgroup and its full centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- The two actual-root propositions imply closed generation by a smooth
connected normal subgroup and its entire scheme-theoretic centralizer. -/
theorem range_eq_top_of_normal_and_centralizer
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    (hG : IsSemisimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hH : SubgroupFunctor.range h ≤ SubgroupFunctor.range d)
    (hC : (AutomorphicAction.conjugation h).fixedSubgroup ≤
      SubgroupFunctor.range d) : SubgroupFunctor.range d = ⊤ := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  apply hRoots k G hG T t hSplit hMax D d hd
  intro α hα
  rcases hDichotomy k G hG T t hSplit hMax H h hh hn α hα with hαH | hαC
  · exact le_trans hαH hH
  · exact le_trans hαC hC

/-- Construct an actual isomorphism from any closed subgroup containing the
normal subgroup and full centralizer, conditional on the two root propositions.
Its forward map is the original closed inclusion. -/
def normalCentralizerGenerationIso
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    (hG : IsSemisimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hH : SubgroupFunctor.range h ≤ SubgroupFunctor.range d)
    (hC : (AutomorphicAction.conjugation h).fixedSubgroup ≤
      SubgroupFunctor.range d) : D ≅ G := by
  letI : IsClosedImmersion d.hom.hom.left := hd
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy d :=
    ⟨Over.mono_of_mono_left _, range_eq_top_of_normal_and_centralizer
      hRoots hDichotomy hG T t hSplit hMax h hh hn d hd hH hC⟩
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro U
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨x, Category.comp_id x⟩
  exact hrep.isoOfIsRepresentedBy hid

/-- The isomorphism realizes precisely the original closed inclusion. -/
theorem normalCentralizerGenerationIso_hom
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hDichotomy : SemisimpleNormalRootDichotomyStatement.{u})
    (hG : IsSemisimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hH : SubgroupFunctor.range h ≤ SubgroupFunctor.range d)
    (hC : (AutomorphicAction.conjugation h).fixedSubgroup ≤
      SubgroupFunctor.range d) :
    (normalCentralizerGenerationIso hRoots hDichotomy hG T t hSplit hMax
      h hh hn d hd hH hC).hom = d := by
  unfold normalCentralizerGenerationIso
  simpa only [Category.comp_id] using
    (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp
      (i := d) (i₂ := 𝟙 G) _ _)

end Langlands.GroupScheme
