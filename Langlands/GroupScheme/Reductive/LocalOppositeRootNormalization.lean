import Langlands.GroupScheme.Reductive.OppositePowerRigidity
import Langlands.GroupScheme.Reductive.LocalRankOneWeylNormalization
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws
import Langlands.GroupScheme.Reductive.SplitBorelPositiveCoordinates

/-! # Normalized opposite-root Gauss relations over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace OppositePower

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
  {I : Type u} [Fintype I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- A normalized Gauss relation whose middle factor is the supplied exponent
cocharacter, on every scheme test. -/
def HasCorootGaussRelation
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (nu : I → ℤ) (xp xm : Ga R ⟶ G) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤))
    (d : Γ(Z.left, ⊤)ˣ), (d : Γ(Z.left, ⊤)) = 1 + x * y →
    rootPoint xp Z x * rootPoint xm Z y =
      rootPoint xm Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) *
        ((cocharPoint nu Z d ≫ i.hom.hom) *
          rootPoint xp Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * x))

theorem HasCorootGaussRelation.hasGaussRelation
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {nu : I → ℤ} {xp xm : Ga R ⟶ G}
    (h : HasCorootGaussRelation i nu xp xm) :
    HasGaussRelation (T := splitTorus.commGroupScheme _ I) i xp xm := by
  intro Z x y d hd
  exact ⟨cocharPoint nu Z d, h Z x y d hd⟩

/-- The Gauss clause of the existing all-test rank-one laws. -/
theorem hasCorootGaussRelation_of_rankOneLaws
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {nu : I → ℤ} {xp xm : Ga R ⟶ G}
    (h : RankOneLaws i nu xp xm) : HasCorootGaussRelation i nu xp xm := by
  intro Z x y d hd
  simpa only [mul_assoc] using h.2.2.2 Z x y d hd

/-- Descent uses actual relative tests and the epimorphic counit of faithful
pullback. It does not use equality on field points. -/
theorem HasCorootGaussRelation.of_baseChange
    (A : Type u) [CommRing A] [Algebra R A]
    [(Over.pullback (algebraBaseMap R A)).Faithful]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (nu : I → ℤ) (xp xm : Ga R ⟶ G)
    (h : HasCorootGaussRelation (splitTorus.baseChangeHom (K := A) G I i) nu
      (baseChangeRoot A xp) (baseChangeRoot A xm)) :
    HasCorootGaussRelation i nu xp xm := by
  intro Z x y d hd
  let W := (Over.pullback (algebraBaseMap R A)).obj Z
  let j : (Over.map (algebraBaseMap R A)).obj W ⟶ Z :=
    (Over.mapPullbackAdj (algebraBaseMap R A)).counit.app Z
  have : Epi j :=
    inferInstanceAs (Epi ((Over.mapPullbackAdj (algebraBaseMap R A)).counit.app Z))
  apply (cancel_epi j).1
  simp only [MonObj.comp_mul, comp_rootPoint, ← Category.assoc,
    comp_cocharPoint, map_mul]
  let res : Γ(Z.left, ⊤) →+* Γ(W.left, ⊤) := j.left.appTop.hom
  let d' := Units.map res.toMonoidHom d
  have hd' : (d' : Γ(W.left, ⊤)) = 1 + res x * res y := by
    change res (d : Γ(Z.left, ⊤)) = _
    rw [hd, map_add, map_one, map_mul]
  have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G W)
    (h W (res x) (res y) d' hd')
  simp only [map_mul, baseChangePointsEquiv_rootPoint,
    baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint,
    d', Units.coe_map_inv] at e
  convert e using 1

/-- The coroot formula survives composition into an ambient group. -/
theorem HasCorootGaussRelation.comp
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {nu : I → ℤ} {xp xm : Ga R ⟶ G}
    (h : HasCorootGaussRelation i nu xp xm) (e : G ⟶ H) :
    HasCorootGaussRelation (i ≫ e) nu (xp ≫ e) (xm ≫ e) := by
  intro Z x y d hd
  have he := congrArg (fun p => p ≫ e.hom.hom) (h Z x y d hd)
  simpa only [MonObj.mul_comp, rootPoint_comp, Grp.comp_hom_hom,
    Category.assoc] using he

/-- Coordinate separation passes through a monomorphic ambient inclusion. -/
theorem SeparatesPositive.comp
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ G} {xp xm : Ga R ⟶ G}
    (h : SeparatesPositive i xp xm) (e : G ⟶ H) [Mono e.hom.hom] :
    SeparatesPositive (i ≫ e) (xp ≫ e) (xm ≫ e) := by
  intro Z y y' x x' t t' he
  apply h Z y y' x x' t t'
  apply (cancel_mono e.hom.hom).1
  simpa only [MonObj.mul_comp, rootPoint_comp, Grp.comp_hom_hom,
    Category.assoc] using he

/-- Rescaling the negative coordinate preserves separation of the positive
coordinate. -/
theorem SeparatesPositive.scaleNegative
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {i : T.toGrp ⟶ G} {xp xm : Ga R ⟶ G}
    (h : SeparatesPositive i xp xm) (d : R) :
    SeparatesPositive i xp (scaleHom d ≫ xm) := by
  intro Z y y' x x' t t' he
  simp only [rootPoint_scaleHom] at he
  exact h Z _ _ _ _ _ _ he

end OppositePower

namespace RingRootCell.WeylData

open LocalSplitCell

variable {R : Type u} [CommRing R] (W : WeylData R)

/-- The ring-calculus beta coefficient is the base scalar of its actual unit. -/
theorem pb_cβ_eq_baseScalar (Z : Over (Spec (CommRingCat.of R))) :
    pb Z W.cβ = baseScalar Z (W.betaUnit : R) := by
  rw [W.betaUnit_val]
  have hβ : W.cβ = baseScalar (base R)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom W.cβ) := by
    change W.cβ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom W.cβ)
    exact (Iso.hom_inv_id_apply _ _).symm
  conv_lhs => rw [hβ]
  rw [pb]
  exact appTop_baseScalar (toBase Z) _

/-- The normalized ring rank-one pair has the required Gauss relation. -/
theorem hasGaussRelation [IsAffine W.G.X.left] :
    OppositePower.HasGaussRelation W.i W.xp (scaleHom (W.betaUnit : R) ≫ W.xm) := by
  intro Z x y d hd
  refine ⟨W.tH d, ?_⟩
  have h := W.relation x y d hd
  simp only [rootPoint_scaleHom]
  simpa only [rootPoint, CellData.A, CellData.B, CellData.I,
    CellData.cellPt, pb_cβ_eq_baseScalar, mul_assoc] using h

/-- The open cell belongs to the rank-one group; its injectivity separates
positive coordinates also after negative-coordinate normalization. -/
theorem separatesPositive :
    OppositePower.SeparatesPositive W.i W.xp
      (scaleHom (W.betaUnit : R) ≫ W.xm) := by
  apply OppositePower.SeparatesPositive.scaleNegative
  intro Z y y' x x' t t' h
  exact (W.cellPt_inj h).2.2

end RingRootCell.WeylData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange LocalWeylNormalization OppositePower

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

/-- The ring-calculus Gauss relation has the prescribed coroot on the affine
etale coefficient ring. -/
theorem affineEtale_hasCorootGaussRelation (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
    HasCorootGaussRelation W.i (P.coroot a) W.xp
      (scaleHom (W.betaUnit : E.ring) ≫ W.xm) := by
  let := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange (algebraBaseMap R E.ring)).obj C).X.hom)
    exact inferInstanceAs
      (IsAffineHom (Limits.pullback.snd C.X.hom (algebraBaseMap R E.ring)))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  change HasCorootGaussRelation W.i (P.coroot a) W.xp
    (scaleHom (W.betaUnit : E.ring) ≫ W.xm)
  intro Z x y d hd
  have ht : W.tH d = cocharPoint (P.coroot a) Z d := by
    exact (cocharPoint_eq_comp (P.coroot a) Z d).symm
  have h := W.relation x y d hd
  simp only [rootPoint_scaleHom]
  simpa only [rootPoint, RingRootCell.CellData.A, RingRootCell.CellData.B,
    RingRootCell.CellData.I, RingRootCell.CellData.cellPt,
    RingRootCell.WeylData.pb_cβ_eq_baseScalar, ht, mul_assoc] using h

/-- The coroot Gauss formula descends with the same scalar that gives the
normalizing point. -/
theorem scalar_hasCorootGaussRelation (hi : IsClosedSubgroup i) (d : R)
    (hd : letI := E.coefficientAlgebra
      algebraMap R E.ring d =
        ((affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).betaUnit : E.ring)) :
    HasCorootGaussRelation (torusHom I G i mu) (P.coroot a)
      (rootLift i mu hp ha)
      (scaleHom d ≫ rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) := by
  let := E.coefficientAlgebra
  let b := algebraBaseMap R E.ring
  let : Etale b := by
    change Etale (algebraBaseMap R E.ring)
    rw [E.coefficientAlgebra_baseMap]
    exact E.etale
  let : Surjective b := by
    change Surjective (algebraBaseMap R E.ring)
    rw [E.coefficientAlgebra_baseMap]
    exact ⟨E.projection_surjective⟩
  apply HasCorootGaussRelation.of_baseChange E.ring
  rw [LocalSplitRootBaseChange.baseChangeRoot_scaleHom, hd]
  exact affineEtale_hasCorootGaussRelation i mu hG hmax hP a ha hmu hp hm E hi

include E in
/-- A single unit scalar gives both the coroot Gauss relation and the
reflection identity over the original local ring. -/
theorem exists_gauss_normalizing_scalar (hi : IsClosedSubgroup i)
    {y : Γ((dualOver R).left, ⊤)}
    {t : dualOver R ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X}
    {x : Γ((dualOver R).left, ⊤)}
    (hx : (corootCellData i mu hG hmax hP a ha hmu hp hm).A 1 *
        (corootCellData i mu hG hmax hP a ha hmu hp hm).B (epsSec R) =
      (corootCellData i mu hG hmax hP a ha hmu hp hm).cellPt y t x) :
    ∃ d : Rˣ,
      HasCorootGaussRelation (torusHom I G i mu) (P.coroot a)
        (rootLift i mu hp ha)
        (scaleHom (d : R) ≫ rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) ∧
      IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
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
  have hd : algebraMap R E.ring (↑hc.unit⁻¹ : R) = (W.betaUnit : E.ring) := by
    change (Units.map (algebraMap R E.ring).toMonoidHom hc.unit⁻¹ : E.ring) = _
    rw [map_inv, hmap, inv_inv]
  exact ⟨hc.unit⁻¹,
    scalar_hasCorootGaussRelation i mu hG hmax hP a ha hmu hp hm E hi _ hd,
    scalarWeylPoint_isNormalizing i mu hG hmax hP a ha hmu hp hm E hi _ hd⟩

include hG hmax hmu in
/-- The pointed etale and dual-number constructions supply all auxiliary
data for simultaneous normalization over an arbitrary local ring. -/
theorem exists_gauss_normalizing_scalar_local (hi : IsClosedSubgroup i) :
    ∃ d : Rˣ,
      HasCorootGaussRelation (torusHom I G i mu) (P.coroot a)
        (rootLift i mu hp ha)
        (scaleHom (d : R) ≫ rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha)) ∧
      IsNormalizingPoint (T := commGroupScheme _ I) (torusHom I G i mu)
        (scalarWeylPoint (rootLift i mu hp ha)
          (rootLift i mu hm (by
            simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
              congrArg Neg.neg ha)) (d : R))
        (LocalRankOneWeylData.corootReflectionIso hP a) := by
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  let p := pointedEtaleUnitCellReflection i mu hG hmax hP a ha hmu hp hm hi
    (IsLocalRing.closedPoint R)
  let E := p.affineEtaleUnitCell
  obtain ⟨y, t, x, hx⟩ := D.exists_dualFactorization
  exact exists_gauss_normalizing_scalar i mu hG hmax hP a ha hmu hp hm E hi hx

end splitTorus.RelativeCocharacterCentralizer

namespace LocalSplitCell

open OppositePower splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)

include hG hi hmax hP hp hm in
/-- Actual opposite root parametrizations over any local ring admit a unit
normalization with the coroot Gauss relation, ambient positive-coordinate
separation, and the prescribed Weyl reflection, for the same normalized pair. -/
theorem exists_unit_oppositeNormalization :
    ∃ d : Rˣ,
      HasCorootGaussRelation i (P.coroot a) xp (scaleHom (d : R) ≫ xm) ∧
      SeparatesPositive (U := splitTorus.commGroupScheme _ I) i xp
        (scaleHom (d : R) ≫ xm) ∧
      IsWeylPoint i (weylPoint xp (scaleHom (d : R) ≫ xm)) (P.reflection a) := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ :=
    LocalRootGroup.exists_kernel_exponent P (IsLocalRing.ResidueField R) a
  obtain ⟨d, hg, hn⟩ :=
    exists_gauss_normalizing_scalar_local i mu hG hmax hP a ha hmu hp hm hi
  let e := inclusion I G i mu
  let : IsClosedImmersion e.hom.hom.left := isClosedSubgroup_inclusion I G i mu
  let : Mono e.hom.hom := Over.mono_of_mono_left _
  have hgauss := hg.comp e
  rw [torusHom_comp, rootLift_comp, Category.assoc, rootLift_comp] at hgauss
  have hs : SeparatesPositive (U := splitTorus.commGroupScheme _ I)
      (torusHom I G i mu) (rootLift i mu hp ha)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) := by
    intro Z y y' x x' t t' h
    exact ((corootCellData i mu hG hmax hP a ha hmu hp hm).cellPt_inj h).2.2
  have hsep := (hs.scaleNegative (d : R)).comp e
  rw [torusHom_comp, rootLift_comp, Category.assoc, rootLift_comp] at hsep
  refine ⟨d, hgauss, hsep, isWeylPoint_of_isNormalizingPoint ?_⟩
  have h := hn.comp e
  rw [torusHom_comp, LocalRankOneWeylData.corootReflectionIso,
    LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a] at h
  change IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i
    (weylPoint (rootLift i mu hp ha) (scaleHom (d : R) ≫ rootLift i mu hm _) ≫
      e.hom.hom) _ at h
  rw [← weylPoint_comp, rootLift_comp, Category.assoc, rootLift_comp] at h
  exact h

end LocalSplitCell

end Langlands.GroupScheme
