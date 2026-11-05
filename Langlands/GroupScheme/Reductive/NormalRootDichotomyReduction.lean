import Langlands.GroupScheme.Reductive.CompatibleNormalTorus
import Langlands.GroupScheme.Reductive.NormalRootContainment
import Langlands.GroupScheme.Reductive.RootGeneratedCentralizer
import Langlands.GroupScheme.Reductive.NormalSemisimpleReduction
import Langlands.GroupScheme.Reductive.NormalRootDichotomyStatement
import Langlands.GroupScheme.Reductive.AlmostSimpleGenerationReduction
import Langlands.GroupScheme.Absolute.RootVectorLineStatement
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyReduction

/-! # Normal-root dichotomy from actual root lines and maximal-torus conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The exact all-test normal-root dichotomy follows from four explicit
structural premises. In particular, root-line realization and conjugacy are
not replaced by abstract root-system data. -/
theorem semisimpleNormalRootDichotomy_of_rootLines
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hLines : AbsoluteRootVectorLineStatement.{u})
    (hConj : MaximalTorusConjugacyStatement.{u}) :
    SemisimpleNormalRootDichotomyStatement.{u} := by
  intro k _ _ G hG
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hG.isConnectedReductive.connectedSpace
  intro T t hSplit hMax H _ _ h hh hn α hα
  let : IsAffineHom H.X.hom := hh.isAffineHom
  let : IsClosedImmersion h.hom.hom.left := hh
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  have hH : IsSemisimple H :=
    hG.of_normalSubgroup_of_normalReductiveCenterStatement hCenter h hh hn
  have hconj : MaximalToriAreConjugate G := by
    intro M M' m m' hm hm'
    exact (subgroupConjugate_iff_exists_commGroupSchemeIso m m').mpr
      (hConj k G M M' m m' hm hm')
  let d := compatibleNormalMaximalTorusOfConjugacy hconj h hh hn t hMax
  have hs := d.isSplitSubtorus
  rcases RelativeRoot.subgroup_le_range_or_fixedSubgroup
    d.torusHom t d.subgroupHom h hs.1 hh hn d.comp_eq α with hIn | hFix
  · exact Or.inl hIn
  right
  obtain ⟨U, a, ha, _, hU⟩ :=
    hLines k G hG.isConnectedReductive T t hSplit hMax α hα
  have hnU : (SubgroupFunctor.range h).IsNormalizedBy (SubgroupFunctor.range a) :=
    fun V g x _ hx => hn V g x (by trivial) hx
  have hc : SubgroupFunctor.range a ≤
      (AutomorphicAction.conjugation (d.subgroupHom ≫ h)).fixedSubgroup := by
    rw [ha.2]
    exact hFix
  rw [← ha.2]
  apply range_le_centralizer_of_rootGeneration_vectorLines
    hRoots hH d.torus d.subgroupHom hs d.isMaximalTorus h a hnU hc hU
  intro β hβ
  obtain ⟨V, j, hj, _, hV⟩ :=
    hLines k H hH.isConnectedReductive d.torus d.subgroupHom
      hs d.isMaximalTorus β hβ
  exact ⟨V, j, hj, hV⟩

/-- The published dimension-induction assembly specializes the conditional
normal-root dichotomy to the exact host generation statement. -/
theorem semisimpleAlmostSimpleGeneration_of_rootLines
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hLines : AbsoluteRootVectorLineStatement.{u})
    (hConj : MaximalTorusConjugacyStatement.{u}) :
    SemisimpleAlmostSimpleGenerationStatement.{u} :=
  semisimpleAlmostSimpleGeneration_of_actualRoots hCenter hRoots
    (semisimpleNormalRootDichotomy_of_rootLines hCenter hRoots hLines hConj)

section Placement

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H U C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]

/-- For an actual representative of an ambient root, construct a map into
either the original normal subgroup or any supplied representative of its
full centralizer. The chosen map has the original ambient composite. -/
def normalRootPlacementOfRootLines
    (hCenter : NormalReductiveCenterStatement.{u})
    (hRoots : SemisimpleRootGenerationStatement.{u})
    (hLines : AbsoluteRootVectorLineStatement.{u})
    (hConj : MaximalTorusConjugacyStatement.{u})
    (hG : IsSemisimple G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G)
    (hSplit : IsSplitSubtorus t) (hMax : IsMaximalTorus t)
    (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (α : characterLattice T) (hα : α ∈ relativeRoots t)
    (a : U ⟶ G) (ha : (RelativeRoot.subgroup t α).IsRepresentedBy a)
    (c : C ⟶ G)
    (hc : (AutomorphicAction.conjugation h).fixedSubgroup.IsRepresentedBy c) :
    {f : U ⟶ H // f ≫ h = a} ⊕ {f : U ⟶ C // f ≫ c = a} := by
  classical
  let : IsClosedImmersion h.hom.hom.left := hh
  have hr : (SubgroupFunctor.range h).IsRepresentedBy h :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  by_cases hIn : RelativeRoot.subgroup t α ≤ SubgroupFunctor.range h
  · exact Sum.inl
      ⟨ha.lift hr (fun V => Subgroup.inclusion (hIn V)) (fun _ _ => rfl),
        ha.lift_comp_eq hr (fun V => Subgroup.inclusion (hIn V))
          (fun _ _ => rfl) (fun _ _ => rfl)⟩
  · have hFix := (semisimpleNormalRootDichotomy_of_rootLines hCenter hRoots hLines hConj
      k G hG T t hSplit hMax H h hh hn α hα).resolve_left hIn
    exact Sum.inr
      ⟨ha.lift hc (fun V => Subgroup.inclusion (hFix V)) (fun _ _ => rfl),
        ha.lift_comp_eq hc (fun V => Subgroup.inclusion (hFix V))
          (fun _ _ => rfl) (fun _ _ => rfl)⟩

end Placement

end Langlands.GroupScheme
