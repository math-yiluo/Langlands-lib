import Langlands.GroupScheme.Reductive.NonAffineUnipotentKernelQuotient
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedUnipotentRadicalExtension
import Langlands.GroupScheme.Derived.CentralIntersectionReduction

/-! # Radical extension through a supplied smooth quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A closed representative with the same all-test image as a represented
radical is a radical. -/
theorem IsUnipotentRadical.of_range_eq
    {k : Type u} [Field k]
    {G U V : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} (hi : IsUnipotentRadical i) {j : V ⟶ G}
    (hj : IsClosedSubgroup j)
    (hr : SubgroupFunctor.range i = SubgroupFunctor.range j) :
    IsUnipotentRadical j := by
  rw [← hj.sourceIsoOfRangeEq_hom_comp hi.isClosedSubgroup hr.symm]
  exact hi.precomp_iso (hj.sourceIsoOfRangeEq hi.isClosedSubgroup hr.symm)

/-- A represented radical is preserved under an algebraically closed extension
if a supplied smooth quotient has affine smooth connected target and smooth
connected unipotent actual kernel before and after extension. -/
theorem IsUnipotentRadical.baseChange_of_isAlgClosed_of_smooth_quotient
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (hqK : HasSmoothConnectedUnipotentKernel
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map q))
    {i : U ⟶ G} (hi : IsUnipotentRadical i) :
    IsUnipotentRadical
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have : Smooth (B.obj Q).X.hom := by
    change Smooth (pullback.snd Q.X.hom b)
    infer_instance
  have : IsAffineHom (B.obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  have : Smooth (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Smooth) b q.hom.hom inferInstance
  have : Surjective (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  have : QuasiCompact (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @QuasiCompact) b q.hom.hom inferInstance
  obtain ⟨V, j, hj⟩ := unipotentRadicalExistence k Q
  have hjK : IsUnipotentRadical (B.map j) :=
    hj.baseChange_of_isAlgClosed_of_smooth_affine (K := K)
  have hpK := SmoothUnipotentQuotient.isUnipotentRadical_preimage
    (B.map q) hqK (B.map j) hjK
  have hr : SubgroupFunctor.range (B.map i) =
      SubgroupFunctor.range (SubgroupPreimage.inclusion (B.map q) (B.map j)) := by
    calc
      SubgroupFunctor.range (B.map i) =
          (SubgroupFunctor.range i).baseChange b :=
        SubgroupFunctor.range_baseChangeHom b i
      _ = ((SubgroupFunctor.range j).comap q).baseChange b := by
        rw [SmoothUnipotentQuotient.radical_comap_eq q hq hi hj]
      _ = ((SubgroupFunctor.range j).baseChange b).comap (B.map q) :=
        SubgroupFunctor.comap_baseChange b q (SubgroupFunctor.range j)
      _ = (SubgroupFunctor.range (B.map j)).comap (B.map q) := by
        rw [SubgroupFunctor.range_baseChangeHom]
      _ = SubgroupFunctor.range
          (SubgroupPreimage.inclusion (B.map q) (B.map j)) :=
        (SubgroupPreimage.range_inclusion _ _).symm
  exact hpK.of_range_eq (hi.isClosedSubgroup.baseChange b) hr.symm

namespace SmoothUnipotentQuotient

/-- Actual comparison with any radical representative after the extension,
under the supplied smooth quotient hypotheses. -/
def radicalBaseChangeIso
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (hqK : HasSmoothConnectedUnipotentKernel
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map q))
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj U ≅ V :=
  let h := hi.baseChange_of_isAlgClosed_of_smooth_quotient q hq hqK
  h.isClosedSubgroup.sourceIsoOfRangeEq hj.isClosedSubgroup (h.range_eq hj)

/-- The actual comparison commutes with the subgroup inclusions. -/
@[reassoc]
theorem radicalBaseChangeIso_hom_comp
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    {G Q U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q) [Smooth q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hq : HasSmoothConnectedUnipotentKernel q)
    (hqK : HasSmoothConnectedUnipotentKernel
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map q))
    {i : U ⟶ G} (hi : IsUnipotentRadical i)
    {V : GroupScheme (Spec (CommRingCat.of K))}
    {j : V ⟶ (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}
    (hj : IsUnipotentRadical j) :
    (radicalBaseChangeIso q hq hqK hi hj).hom ≫ j =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i := by
  let h := hi.baseChange_of_isAlgClosed_of_smooth_quotient q hq hqK
  exact IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp
    h.isClosedSubgroup hj.isClosedSubgroup (h.range_eq hj)

end SmoothUnipotentQuotient
end Langlands.GroupScheme
