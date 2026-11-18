import Langlands.GroupScheme.Reductive.NormalRootDichotomyProof
import Langlands.GroupScheme.Reductive.CentralizerDerivedComparison
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SemisimpleFieldExtensionProof
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # The actual normal-root dichotomy for a split maximal torus over any field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [Smooth H.X.hom] [ConnectedSpace H.X.left]
  (hG : IsSemisimple G)
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
  (j : H ⟶ G) (hj : IsClosedSubgroup j) (hn : (SubgroupFunctor.range j).IsNormal)

include hG hT ht hj hn

/-- Every actual root subgroup of a split maximal torus over an arbitrary
field is contained in a smooth connected normal subgroup or centralizes it. -/
theorem splitNormalRootDichotomy (α : characterLattice T) (hα : α ∈ relativeRoots t) :
    RelativeRoot.subgroup t α ≤ SubgroupFunctor.range j ∨
      RelativeRoot.subgroup t α ≤ (AutomorphicAction.conjugation j).fixedSubgroup := by
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k G hG.isConnectedReductive T hT t ht
  obtain ⟨r, rfl⟩ : α ∈ Set.range P.root := by
    rw [hP.2.1, ← relativeRoots_eq_roots]
    exact hα
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  obtain ⟨hbS, hbF, hbQ⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbS
  let : Flat b := hbF
  let : QuasiCompact b := hbQ
  let GK := (GroupScheme.baseChange b).obj G
  let HK := (GroupScheme.baseChange b).obj H
  let TK := (CommGroupScheme.baseChange b).obj T
  let tK := (GroupScheme.baseChange b).map t
  let jK := (GroupScheme.baseChange b).map j
  have hGK : IsSemisimple GK := isSemisimpleFieldExtension k K G hG
  let : Smooth HK.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd H.X.hom b)
    infer_instance
  let : ConnectedSpace HK.X.left := H.connectedSpace_baseChange_of_smooth_affine b
  have htK : IsMaximalTorus (T := TK) tK :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  have hnK : (SubgroupFunctor.range jK).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hPK := hP.baseChange (K := K) G T hT t
  have hrK : characterLattice.baseChange b T (P.root r) ∈ relativeRoots tK := by
    rw [relativeRoots_eq_roots, ← hPK.2.1]
    exact ⟨r, rfl⟩
  rcases semisimpleNormalRootDichotomy K GK hGK TK tK
      ⟨hT.baseChange b, htK.2.1⟩ htK HK jK (hj.baseChange b) hnK
      (characterLattice.baseChange b T (P.root r)) hrK with hin | hfix
  · left
    apply SubgroupFunctor.le_range_of_baseChange_le b j
    rw [← SubgroupFunctor.range_baseChangeHom, ← RelativeRoot.subgroup_baseChange]
    exact hin
  · right
    let C := closedNormalCentralizer j hn
    let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedSubgroup
    let : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
    have hc : RelativeRoot.subgroup t (P.root r) ≤ SubgroupFunctor.range C.inclusion := by
      apply SubgroupFunctor.le_range_of_baseChange_le b C.inclusion
      rw [C.range_eq, ← conjugation_fixedSubgroup_baseChange, ← RelativeRoot.subgroup_baseChange]
      exact hfix
    exact hc.trans_eq C.range_eq

/-- The arbitrary-field split normal-root dichotomy as actual maps from a
supplied root-group representative into the normal subgroup or its full centralizer. -/
def splitNormalRootPlacement {U C : GroupScheme (Spec (CommRingCat.of k))}
    (α : characterLattice T) (hα : α ∈ relativeRoots t)
    (a : U ⟶ G) (ha : (RelativeRoot.subgroup t α).IsRepresentedBy a)
    (c : C ⟶ G) (hc : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy c) :
    {f : U ⟶ H // f ≫ j = a} ⊕ {f : U ⟶ C // f ≫ c = a} := by
  classical
  let : IsClosedImmersion j.hom.hom.left := hj
  have hr : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  by_cases hin : RelativeRoot.subgroup t α ≤ SubgroupFunctor.range j
  · exact Sum.inl
      ⟨ha.lift hr (fun V => Subgroup.inclusion (hin V)) (fun _ _ => rfl),
        ha.lift_comp_eq hr (fun V => Subgroup.inclusion (hin V))
          (fun _ _ => rfl) (fun _ _ => rfl)⟩
  · have hfix := (splitNormalRootDichotomy hG t hT ht j hj hn α hα).resolve_left hin
    exact Sum.inr
      ⟨ha.lift hc (fun V => Subgroup.inclusion (hfix V)) (fun _ _ => rfl),
        ha.lift_comp_eq hc (fun V => Subgroup.inclusion (hfix V))
          (fun _ _ => rfl) (fun _ _ => rfl)⟩

end Langlands.GroupScheme
