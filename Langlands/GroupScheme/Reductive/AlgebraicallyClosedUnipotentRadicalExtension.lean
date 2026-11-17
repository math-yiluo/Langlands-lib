import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.Reductive.RadicalFieldExtensionProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Rational.KernelCentralizerRadicalComparison
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.AbelianScheme.KernelBaseChange

/-! # Represented affine radicals under algebraically closed extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Over algebraically closed fields, a represented radical of a smooth
connected affine group remains a radical under arbitrary field extension. -/
theorem IsUnipotentRadical.baseChange_of_isAlgClosed_of_smooth_affine
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : IsUnipotentRadical i) :
    IsUnipotentRadical
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hi.smooth
  let : ConnectedSpace U.X.left := hi.connectedSpace
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  let : Smooth Q.X.hom := hQ.smooth
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : ConnectedSpace Q.X.left := hQ.connectedSpace
  let : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  let : LocallyOfFiniteType ((GroupScheme.baseChange b).obj Q).X.hom := by
    change LocallyOfFiniteType (pullback.snd Q.X.hom b)
    infer_instance
  let : Flat ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom hq.1
  let : Surjective ((GroupScheme.baseChange b).map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hq.2.1
  have hQK : HasTrivialUnipotentRadical ((GroupScheme.baseChange b).obj Q) :=
    algebraicallyClosedRadicalFieldExtensionStatement k K Q
      hQ.smooth hQ.isAffineHom hQ.connectedSpace hQ.hasTrivialUnipotentRadical
  obtain ⟨V, j, hj⟩ := unipotentRadicalExistence K ((GroupScheme.baseChange b).obj G)
  have hclosed : IsClosedSubgroup ((GroupScheme.baseChange b).map i) :=
    hi.isClosedSubgroup.baseChange b
  have hker : SubgroupFunctor.range
      (kernelι ((GroupScheme.baseChange b).map q)) =
      SubgroupFunctor.range ((GroupScheme.baseChange b).map i) := by
    rw [← SubgroupFunctor.range_iso_precomp (kernelBaseChangeIso b q),
      kernelBaseChangeIso_hom_ι, SubgroupFunctor.range_baseChangeHom,
      hq.2.2.2, SubgroupFunctor.range_baseChangeHom]
  have hr : SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
      SubgroupFunctor.range j := by
    apply le_antisymm
    · apply hj.greatest _ _ hclosed
      · change Smooth (pullback.snd U.X.hom b)
        infer_instance
      · exact U.connectedSpace_baseChange_of_smooth_affine b
      · exact hi.isUnipotent.baseChange
      · rw [SubgroupFunctor.range_baseChangeHom]
        exact hi.isNormal.baseChange b
    · rw [← hker]
      exact hj.range_le_kernel_of_trivial_target
        ((GroupScheme.baseChange b).map q) hQK
  rw [← hclosed.sourceIsoOfRangeEq_hom_comp hj.isClosedSubgroup hr]
  exact hj.precomp_iso (hclosed.sourceIsoOfRangeEq hj.isClosedSubgroup hr)

/-- The actual source comparison between the base change of a supplied
radical and any radical representative after algebraically closed extension. -/
def IsUnipotentRadical.baseChangeIsoOfIsAlgClosed
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj U ≅ V :=
  let h := hi.baseChange_of_isAlgClosed_of_smooth_affine (K := K)
  h.isClosedSubgroup.sourceIsoOfRangeEq hj.isClosedSubgroup (h.range_eq hj)

/-- The source comparison commutes with the actual subgroup inclusions. -/
theorem IsUnipotentRadical.baseChangeIsoOfIsAlgClosed_hom_comp
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (hi.baseChangeIsoOfIsAlgClosed hj).hom ≫ j =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i :=
  let h := hi.baseChange_of_isAlgClosed_of_smooth_affine (K := K)
  h.isClosedSubgroup.sourceIsoOfRangeEq_hom_comp hj.isClosedSubgroup (h.range_eq hj)

end Langlands.GroupScheme
