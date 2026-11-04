import Langlands.GroupScheme.Absolute.BorelGmQuotients
import Langlands.GroupScheme.Absolute.CentralMultiplicativeQuotientStatement
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.SmoothNormalQuotient
import Langlands.GroupScheme.AffineQuotientProof

/-! # Borel normalizer induction through actual smooth central quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SmoothNormalQuotient

variable {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {i : N ⟶ G}

/-- The actual smooth normal quotient of an affine group is affine. -/
theorem isAffineHom (D : SmoothNormalQuotient i) :
    IsAffineHom D.quotient.X.hom := by
  have : LocallyOfFiniteType D.quotient.X.hom := D.locallyOfFiniteType
  have : QuasiCompact D.quotient.X.hom := D.quasiCompact
  have : IsSeparated D.quotient.X.hom := D.separated
  have : Flat D.projection.hom.hom.left := D.isFppfQuotient.1
  have : Surjective D.projection.hom.hom.left := D.surjective_projection
  have : QuasiCompact D.projection.hom.hom.left := D.quasiCompact_projection
  exact affineGroupSchemeQuotient k G D.quotient D.projection

end SmoothNormalQuotient

section Central

variable {k : Type u} [Field k] [IsAlgClosed k]
    {B G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- A smooth central copy of Gm gives both actual affine quotients without
assuming the general normal-subgroup quotient proposition. -/
theorem exists_borel_quotients_of_smooth_central_gm
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
  let D := SmoothNormalQuotient.ofClosedNormal z hz (smooth_gm _)
    hcentral.range_isNormal
  let E := SmoothNormalQuotient.ofClosedNormal zB hzB (smooth_gm _) hnB
  let : IsAffineHom D.quotient.X.hom := D.isAffineHom
  let : IsAffineHom E.quotient.X.hom := E.isAffineHom
  obtain ⟨j, hj, hsq, hqs, hps, hqc, hpb, hpre⟩ :=
    exists_borel_of_fppf_gm_quotients i hi z hz zB hf
      D.projection D.isFppfQuotient E.projection E.isFppfQuotient
  exact ⟨D.quotient, E.quotient, D.projection, E.projection, j,
    D.smooth, D.isAffineHom, E.smooth, E.isAffineHom,
    D.isFppfQuotient, E.isFppfQuotient,
    hj, hsq, hqs, hps, hqc, hpb, hpre⟩

/-- The exact central quotient and Borel descent statement follows from the
actual smooth normal quotients and the published affine quotient theorem. -/
theorem centralMultiplicativeQuotientBorel :
    CentralMultiplicativeQuotientBorelStatement.{u} := by
  intro k _ _ G _ _ _ B i hi z hz hcentral zB hf
  obtain ⟨Q, BQ, q, p, j, hsQ, haQ, _, _, hq, hp,
      hj, hsq, hqs, hps, _, _, hpre⟩ :=
    exists_borel_quotients_of_smooth_central_gm i hi z hz
      ((isCentral_iff_range_le_center z).mpr hcentral) zB hf
  let : IsAffineHom Q.X.hom := haQ
  obtain ⟨_, _, hcQ, hdim⟩ := hq.gm_induction_properties z hz q
  exact ⟨Q, q, haQ, hsQ, hcQ, hqs, hq, hdim, BQ, j, p,
    hj, hsq, hps, hp, hpre⟩

/-- The central Gm branch needs only the smaller-group induction hypothesis;
its quotient existence is supplied by the published smooth quotient theory. -/
theorem normalizer_borelRange_eq_of_smooth_central_gm
    [ConnectedSpace G.X.left]
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
    exists_borel_quotients_of_smooth_central_gm i hi z hz hcentral zB hf
  let : IsAffineHom Q.X.hom := haQ
  exact normalizer_borelRange_eq_of_fppf_gm_quotient ih i z hz q hq j hj hpre

/-- An actual Borel point above a rational normalizing point in the central
Gm branch, with no general normal-quotient proposition as a premise. -/
def borelPointOfSmoothCentralGm
    [ConnectedSpace G.X.left]
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
    ((normalizer_borelRange_eq_of_smooth_central_gm ih i hi z hz hcentral zB hf) ▸ hx))

/-- The chosen Borel point has the specified ambient image. -/
theorem borelPointOfSmoothCentralGm_comp
    [ConnectedSpace G.X.left]
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
    borelPointOfSmoothCentralGm ih i hi z hz hcentral zB hf x hx ≫ i.hom.hom = x :=
  Classical.choose_spec (SubgroupFunctor.mem_range.mp
    ((normalizer_borelRange_eq_of_smooth_central_gm ih i hi z hz hcentral zB hf) ▸ hx))

end Central

end Langlands.GroupScheme
