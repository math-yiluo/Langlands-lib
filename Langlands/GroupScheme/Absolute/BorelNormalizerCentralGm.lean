import Langlands.GroupScheme.Absolute.BorelGmQuotients
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction

/-! # Borel normalizer induction from a central multiplicative subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] [IsAlgClosed k]
    {B G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- The normal quotient proposition supplies both affine Gm quotients and
their actual Borel embedding. Quotient existence remains an explicit premise. -/
theorem exists_borel_quotients_of_central_gm
    (hquot : NormalSubgroupQuotientStatement.{u})
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z) :
    ∃ (Q BQ : GroupScheme (Spec (CommRingCat.of k)))
      (q : G ⟶ Q) (p : B ⟶ BQ) (j : BQ ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧
      Smooth BQ.X.hom ∧ IsAffineHom BQ.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range zB) p ∧
      IsBorelSubgroup j ∧ i ≫ q = p ≫ j ∧
      Smooth q.hom.hom.left ∧ Smooth p.hom.hom.left ∧
      GeometricallyConnected q.hom.hom.left ∧
      IsPullback i.hom.hom p.hom.hom q.hom.hom j.hom.hom ∧
      (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Smooth B.X.hom := hi.smooth
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsClosedImmersion z.hom.hom.left := hz
  have : IsClosedImmersion (zB.hom.hom.left ≫ i.hom.hom.left) := by
    change IsClosedImmersion (zB ≫ i).hom.hom.left
    rw [hf]
    infer_instance
  have hzB : IsClosedSubgroup zB :=
    IsClosedImmersion.of_comp_isClosedImmersion zB.hom.hom.left i.hom.hom.left
  have hnB : (SubgroupFunctor.range zB).IsNormal := by
    rw [← SubgroupFunctor.comap_range_of_factor i z zB hf]
    exact hcentral.range_isNormal.comap i
  obtain ⟨Q, q, hsQ, haQ, hq⟩ :=
    hquot k G _ z hz hcentral.range_isNormal
  obtain ⟨BQ, p, hsBQ, haBQ, hp⟩ := hquot k B _ zB hzB hnB
  let : IsAffineHom Q.X.hom := haQ
  let : IsAffineHom BQ.X.hom := haBQ
  obtain ⟨j, hj, hsq, hqs, hps, hqc, hpb, hpre⟩ :=
    exists_borel_of_fppf_gm_quotients i hi z hz zB hf q hq p hp
  exact ⟨Q, BQ, q, p, j, hsQ, haQ, hsBQ, haBQ, hq, hp,
    hj, hsq, hqs, hps, hqc, hpb, hpre⟩

/-- A central closed copy of Gm inside the Borel completes this branch of
normalizer induction, conditional only on normal quotient existence. -/
theorem normalizer_borelRange_eq_of_central_gm
    [ConnectedSpace G.X.left]
    (hquot : NormalSubgroupQuotientStatement.{u})
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z) :
    Subgroup.normalizer
        ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
          Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) =
      (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨Q, BQ, q, p, j, _, haQ, _, _, hq, _, hj, _, _, _, _, _, hpre⟩ :=
    exists_borel_quotients_of_central_gm hquot i hi z hz hcentral zB hf
  let : IsAffineHom Q.X.hom := haQ
  exact normalizer_borelRange_eq_of_fppf_gm_quotient ih i z hz q hq j hj hpre

/-- An actual Borel point over a rational normalizing point, obtained by
the central Gm branch with its explicit quotient-existence premise. -/
def borelPointOfCentralGm
    [ConnectedSpace G.X.left]
    (hquot : NormalSubgroupQuotientStatement.{u})
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X :=
  Classical.choose (SubgroupFunctor.mem_range.mp
    ((normalizer_borelRange_eq_of_central_gm hquot ih i hi z hz hcentral zB hf) ▸ hx))

/-- The constructed Borel point maps to the given ambient point. -/
theorem borelPointOfCentralGm_comp
    [ConnectedSpace G.X.left]
    (hquot : NormalSubgroupQuotientStatement.{u})
    (ih : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → BorelNormalizerProperty H)
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (z : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hz : IsClosedSubgroup z) (hcentral : IsCentral z)
    (zB : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B) (hf : zB ≫ i = z)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hx : x ∈ Subgroup.normalizer
      ((SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X))) :
    borelPointOfCentralGm hquot ih i hi z hz hcentral zB hf x hx ≫ i.hom.hom = x :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp
    ((normalizer_borelRange_eq_of_central_gm hquot ih i hi z hz hcentral zB hf) ▸ hx))

end Langlands.GroupScheme
