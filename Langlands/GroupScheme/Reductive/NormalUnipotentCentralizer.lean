import Langlands.GroupScheme.Dynamic.SubgroupMaximality
import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.SplitUnipotentSolvable
import Langlands.GroupScheme.UnitSubgroup

/-! # Normal unipotent subgroups inside cocharacter centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G H Z : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth H.X.hom] [ConnectedSpace H.X.left]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : H ⟶ G) (z : Z ⟶ G)
  (hj : IsClosedSubgroup j) (hz : (Dynamic.centralizer χ).IsRepresentedBy z)
  (hzc : IsClosedSubgroup z) (hn : (SubgroupFunctor.range j).IsNormal)
  (hu : IsUnipotent H)

include χ hj hz hzc hn hu

/-- No parabolic-containment assumption is needed for connectedness of the
cocharacter-fixed intersection of a smooth connected unipotent normal subgroup. -/
theorem connectedSpace_normalUnipotentCentralizer :
    ConnectedSpace (subgroupIntersection j z).X.left := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom H.X.hom := hj.isAffineHom
  have hnχ : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ) :=
    fun T g x _ hx => hn T g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation j χ hnχ
  have hrep := Dynamic.isRepresentedBy_intersectionFst_fixed χ j z hz hzc hnχ
  have hclosed := Dynamic.isClosedSubgroup_intersectionFst j z hzc
  have hsmooth := Dynamic.subgroupIntersection_smooth χ j z hz hzc hnχ
    (inferInstance : Smooth H.X.hom) (inferInstance : IsAffineHom H.X.hom)
  have hsolv : RelativeRoot.IsSolvableScheme H :=
    (perfectFieldUnipotentSplit k H inferInstance hu).isSolvableScheme
  have hT : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp :=
    IsSplitTorus.of_iso (splitTorus.gmIso _) (isSplitTorus_splitTorus PUnit)
  have hstable : a.IsStable a.fixedSubgroup := by
    simpa only [AutomorphicAction.restrict_id] using
      AutomorphicAction.fixed_restrict_isStable a (𝟙 _)
  exact Torus.solvableFixedContainmentConnected k H inferInstance inferInstance inferInstance
    hsolv (Gm (Spec (CommRingCat.of k))) hT a a.fixedSubgroup hstable le_rfl
    (subgroupIntersection j z) (subgroupIntersectionFst j z) hrep hclosed hsmooth

/-- A cocharacter centralizer with trivial unipotent radical has trivial
intersection with every smooth connected unipotent normal ambient subgroup. -/
theorem range_normalUnipotentCentralizer_eq_bot
    (hZ : HasTrivialUnipotentRadical Z) :
    SubgroupFunctor.range (subgroupIntersectionSnd j z) = ⊥ := by
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom H.X.hom := hj.isAffineHom
  have hnχ : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range χ) :=
    fun T g x _ hx => hn T g x (Subgroup.mem_top _) hx
  have hnZ : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range z) :=
    fun T g x _ hx => hn T g x (Subgroup.mem_top _) hx
  exact hZ (subgroupIntersection j z) (subgroupIntersectionSnd j z)
    (Dynamic.isClosedSubgroup_intersectionSnd j z hj)
    (Dynamic.subgroupIntersection_smooth χ j z hz hzc hnχ
      (inferInstance : Smooth H.X.hom) (inferInstance : IsAffineHom H.X.hom))
    (connectedSpace_normalUnipotentCentralizer χ j z hj hz hzc hn hu)
    (unipotentClosedSubgroup k H (subgroupIntersection j z) (subgroupIntersectionFst j z)
      (Dynamic.isClosedSubgroup_intersectionFst j z hzc) hu)
    (Dynamic.range_intersectionSnd_isNormal j z hnZ)

/-- The actual normal-unipotent centralizer intersection is the trivial group
scheme, with the canonical map into the specified centralizer retained. -/
def normalUnipotentCentralizerIsoUnit
    (hZ : HasTrivialUnipotentRadical Z) :
    subgroupIntersection j z ≅ Grp.trivial (Over (Spec (CommRingCat.of k))) := by
  let : IsAffineHom Z.X.hom := hzc.isAffineHom
  let : IsClosedImmersion (subgroupIntersectionSnd j z).hom.hom.left :=
    Dynamic.isClosedSubgroup_intersectionSnd j z hj
  have hrep : (⊥ : SubgroupFunctor Z).IsRepresentedBy (subgroupIntersectionSnd j z) :=
    ⟨Over.mono_of_mono_left _, range_normalUnipotentCentralizer_eq_bot χ j z hj hz hzc hn hu hZ⟩
  let : IsClosedImmersion (kernelUnit Z).hom.hom.left := kernelUnit_isClosedSubgroup Z
  have hunit : (⊥ : SubgroupFunctor Z).IsRepresentedBy (kernelUnit Z) :=
    ⟨Over.mono_of_mono_left _, range_kernelUnit Z⟩
  exact hrep.isoOfIsRepresentedBy hunit

theorem normalUnipotentCentralizerIsoUnit_hom_comp
    (hZ : HasTrivialUnipotentRadical Z) :
    (normalUnipotentCentralizerIsoUnit χ j z hj hz hzc hn hu hZ).hom ≫ kernelUnit Z =
      subgroupIntersectionSnd j z := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme
