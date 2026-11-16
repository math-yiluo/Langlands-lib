import Langlands.GroupScheme.Reductive.LocalRankOneNormalizationUnit
import Langlands.GroupScheme.Reductive.RankOneRingNormalizedWeyl
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Descent of actual rank-one normalizing points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- A prescribed torus action descends along any faithful pullback. -/
theorem IsNormalizingPoint.of_faithfulBaseChange
    {S S' : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
    (b : S' ⟶ S) [(Over.pullback b).Faithful]
    {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint ((GroupScheme.baseChange b).map i)
      (baseChangeBasePoint b G n) ((CommGroupScheme.baseChange b).mapIso σ)) :
    IsNormalizingPoint i n σ := by
  apply (GroupScheme.baseChange b).map_injective
  rw [Functor.map_comp, baseChange_innerIso_hom, Functor.map_comp]
  exact hn


namespace LocalSplitCell

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The Weyl product using scalar `d` to rescale the negative root. -/
def scalarWeylPoint (xp xm : Ga R ⟶ G) (d : R) :
    RingRootCell.base R ⟶ G.X :=
  weylPoint xp (scaleHom d ≫ xm)

/-- The product at an arbitrary test has exactly its rescaled coordinates. -/
theorem constantPoint_scalarWeylPoint (xp xm : Ga R ⟶ G) (d : R)
    (Z : Over (Spec (CommRingCat.of R))) :
    G.constantPoint (scalarWeylPoint xp xm d) Z =
      rootPoint xm Z (-baseScalar Z d) *
        (rootPoint xp Z 1 * rootPoint xm Z (-baseScalar Z d)) := by
  rw [scalarWeylPoint, constantPoint_weylPoint,
    rootPoint_scaleHom, mul_neg_one, mul_assoc]

/-- Coefficient extension preserves the scalar and the actual product. -/
theorem baseChangeBasePoint_scalarWeylPoint (xp xm : Ga R ⟶ G) (d : R)
    (A : Type u) [CommRing A] [Algebra R A] :
    baseChangeBasePoint (algebraBaseMap R A) G (scalarWeylPoint xp xm d) =
      scalarWeylPoint (LocalSplitRootBaseChange.baseChangeRoot A xp)
        (LocalSplitRootBaseChange.baseChangeRoot A xm) (algebraMap R A d) := by
  let b := algebraBaseMap R A
  let G' := (GroupScheme.baseChange b).obj G
  apply (GroupScheme.baseChangePointsEquiv b G (RingRootCell.base A)).injective
  change GroupScheme.baseChangePointsEquiv b G (RingRootCell.base A)
      (G'.constantPoint (baseChangeBasePoint b G (scalarWeylPoint xp xm d))
        (RingRootCell.base A)) = _
  rw [baseChangePointsEquiv_constantPoint, constantPoint_scalarWeylPoint]
  change _ = GroupScheme.baseChangePointsEquiv b G (RingRootCell.base A)
    (G'.constantPoint
      (scalarWeylPoint (LocalSplitRootBaseChange.baseChangeRoot A xp)
        (LocalSplitRootBaseChange.baseChangeRoot A xm) (algebraMap R A d))
      (RingRootCell.base A))
  rw [constantPoint_scalarWeylPoint, map_mul, map_mul,
    LocalSplitRootBaseChange.baseChangePointsEquiv_rootPoint,
    LocalSplitRootBaseChange.baseChangePointsEquiv_rootPoint,
    LocalSplitRootBaseChange.baseScalar_map]

end LocalSplitCell

namespace RingRootCell.WeylData

open LocalSplitCell

variable {R : Type u} [CommRing R] (W : WeylData R)

/-- The unit beta coefficient gives exactly the normalized Weyl product. -/
theorem scalarWeylPoint_betaUnit :
    scalarWeylPoint W.xp W.xm (W.betaUnit : R) =
      W.normalizedWeylPoint (base R) := by
  have hβ : baseScalar (base R) (W.betaUnit : R) = W.cβ := by
    rw [W.betaUnit_val]
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom W.cβ) = W.cβ
    exact Iso.hom_inv_id_apply _ _
  change W.G.constantPoint (scalarWeylPoint W.xp W.xm (W.betaUnit : R))
      (base R) = _
  rw [constantPoint_scalarWeylPoint, hβ]
  rfl

end RingRootCell.WeylData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange LocalWeylNormalization

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField
    (IsLocalRing.closedPoint R)) ⟶ (groupScheme I G i mu).X}
  (E : RingRootCell.AffineEtaleUnitCellData
    (corootCellData i mu hG hmax hP a ha hmu hp hm)
    (LocalRankOneWeylData.corootReflectionIso hP a) (IsLocalRing.closedPoint R) n₀)

/-- The normalized product descends to the actual original centralizer as
soon as its scalar has the prescribed coefficient image. -/
theorem scalarWeylPoint_isNormalizing (hi : IsClosedSubgroup i) (d : R)
    (hd : letI := E.coefficientAlgebra
      algebraMap R E.ring d =
        ((affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).betaUnit : E.ring)) :
    IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
      (scalarWeylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) d)
      (LocalRankOneWeylData.corootReflectionIso hP a) := by
  let := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let b := algebraBaseMap R E.ring
  let : Etale b := by
    change Etale (algebraBaseMap R E.ring)
    rw [E.coefficientAlgebra_baseMap]
    exact E.etale
  let : Surjective b := by
    change Surjective (algebraBaseMap R E.ring)
    rw [E.coefficientAlgebra_baseMap]
    exact ⟨E.projection_surjective⟩
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange b).obj C).X.hom)
    exact inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  apply IsNormalizingPoint.of_faithfulBaseChange b
  change IsNormalizingPoint _ _
    ((CommGroupScheme.baseChange b).mapIso
      (RingRootCell.reflectionIso _ _ (LocalRankOneWeylData.coroot_comp_root hP a)))
  rw [LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a]
  apply splitTorus.isNormalizingPoint_baseChange_of_coordinates
    (torusHom I G i mu) b (P.reflection a)
  have hpull : baseChangeBasePoint b C
      (scalarWeylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) d) =
      W.normalizedWeylPoint (RingRootCell.base E.ring) := by
    rw [baseChangeBasePoint_scalarWeylPoint, hd]
    exact W.scalarWeylPoint_betaUnit
  rw [hpull]
  have hn := W.normalizedWeylPoint_isNormalizing
  have he : RingRootCell.reflectionIso W.α W.h W.hh =
      exponentCommIso (Spec (CommRingCat.of E.ring)) I (P.reflection a) :=
    LocalRankOneWeylData.reflectionIso_eq_exponentCommIso_over hP a E.ring
  rw [he] at hn
  exact hn

include E in
/-- The original dual coefficient determines a unit rescaling whose Weyl
product normalizes the actual centralizer torus over the local ring. -/
theorem exists_normalizing_scalar (hi : IsClosedSubgroup i)
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : (corootCellData i mu hG hmax hP a ha hmu hp hm).A 1 *
        (corootCellData i mu hG hmax hP a ha hmu hp hm).B (epsSec R) =
      (corootCellData i mu hG hmax hP a ha hmu hp hm).cellPt y t x) :
    ∃ d : Rˣ, IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
      (scalarWeylPoint (rootLift i mu hp ha)
        (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) (d : R))
      (LocalRankOneWeylData.corootReflectionIso hP a) := by
  let := E.coefficientAlgebra
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  have hc := isUnit_normalizationScalar i mu hG hmax hP a ha hmu hp hm hi E hx
  have hmap : Units.map (algebraMap R E.ring).toMonoidHom hc.unit = W.betaUnit⁻¹ := by
    apply Units.ext
    change algebraMap R E.ring (hc.unit : R) = _
    rw [hc.unit_spec]
    exact algebraMap_normalizationScalar i mu hG hmax hP a ha hmu hp hm E hi hx
  refine ⟨hc.unit⁻¹, scalarWeylPoint_isNormalizing i mu hG hmax hP a ha hmu hp hm E hi
    (↑hc.unit⁻¹ : R) ?_⟩
  change (Units.map (algebraMap R E.ring).toMonoidHom hc.unit⁻¹ : E.ring) = _
  rw [map_inv, hmap, inv_inv]

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
