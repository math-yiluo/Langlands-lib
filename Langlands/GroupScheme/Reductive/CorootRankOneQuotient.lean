import Langlands.GroupScheme.Reductive.RankOneCellQuotient
import Langlands.GroupScheme.Reductive.LocalRankOneNormalizationUnit
import Langlands.GroupScheme.Reductive.CorootTorusProjection
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # The torus quotient law in actual rank-one centralizers -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G Q : GroupScheme (Spec (CommRingCat.of R))}

/-- Actual negative-root rank-one relations preserve the supplied torus map. -/
def RankOneQuotientLaw (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (xm xp : Ga R ⟶ G) (q : splitTorus (Spec (CommRingCat.of R)) I ⟶ Q) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R)))
    (y y' x x' z : Γ(Z.left, ⊤))
    (t t' : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X),
    (rootPoint xm Z y * (t ≫ i.hom.hom) * rootPoint xp Z x) * rootPoint xm Z z =
      rootPoint xm Z y' * (t' ≫ i.hom.hom) * rootPoint xp Z x' →
    t ≫ q.hom.hom = t' ≫ q.hom.hom

private def refinement {S S' : Scheme.{u}} (b : S' ⟶ S) (Z : Over S) :
    (Over.map b).obj ((Over.pullback b).obj Z) ⟶ Z :=
  Over.homMk (Limits.pullback.fst Z.hom b) (by simp [Limits.pullback.condition])

private theorem point_pullback {S S' : Scheme.{u}} (b : S' ⟶ S)
    (H : GroupScheme S) {Z : Over S} (g : Z ⟶ H.X) :
    GroupScheme.baseChangePointsEquiv b H ((Over.pullback b).obj Z)
      ((Over.pullback b).map g) = refinement b Z ≫ g := by
  apply Over.OverMorphism.ext
  simp [refinement]

open LocalSplitRootBaseChange

/-- The actual coordinate rank-one quotient law descends through faithful
  scalar base change. -/
theorem RankOneQuotientLaw.of_faithfulBaseChange
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (xm xp : Ga R ⟶ G) (q : splitTorus (Spec (CommRingCat.of R)) I ⟶ Q)
    (A : Type u) [CommRing A] [Algebra R A]
    [(Over.pullback (algebraBaseMap R A)).Faithful]
    (hlaw : RankOneQuotientLaw (splitTorus.baseChangeHom (K := A) G I i)
      (baseChangeRoot A xm) (baseChangeRoot A xp)
      (splitTorus.baseChangeHom (K := A) Q I q)) :
    RankOneQuotientLaw i xm xp q := by
  intro Z y y' x x' z t t' hxy
  let b := algebraBaseMap R A
  let Z' := (Over.pullback b).obj Z
  let p := refinement b Z
  let ta := (GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z').symm
    (p ≫ t) ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  let tb := (GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z').symm
    (p ≫ t') ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  have ht : GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z'
      (ta ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) = p ≫ t := by
    dsimp only [ta]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
    exact (GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z').apply_symm_apply _
  have ht' : GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z'
      (tb ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) = p ≫ t' := by
    dsimp only [tb]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
      Category.comp_id]
    exact (GroupScheme.baseChangePointsEquiv b (splitTorus _ I) Z').apply_symm_apply _
  have hrel :
      (rootPoint (baseChangeRoot A xm) Z' (p.left.appTop y) *
        (ta ≫ (splitTorus.baseChangeHom (K := A) G I i).hom.hom) *
        rootPoint (baseChangeRoot A xp) Z' (p.left.appTop x)) *
        rootPoint (baseChangeRoot A xm) Z' (p.left.appTop z) =
      rootPoint (baseChangeRoot A xm) Z' (p.left.appTop y') *
        (tb ≫ (splitTorus.baseChangeHom (K := A) G I i).hom.hom) *
        rootPoint (baseChangeRoot A xp) Z' (p.left.appTop x') := by
    apply (GroupScheme.baseChangePointsEquiv b G Z').injective
    simp only [map_mul]
    rw [baseChangePointsEquiv_rootPoint A xm Z' (p.left.appTop y),
      baseChangePointsEquiv_rootPoint A xp Z' (p.left.appTop x),
      baseChangePointsEquiv_rootPoint A xm Z' (p.left.appTop z),
      baseChangePointsEquiv_rootPoint A xm Z' (p.left.appTop y'),
      baseChangePointsEquiv_rootPoint A xp Z' (p.left.appTop x'),
      baseChangePointsEquiv_torus A i ta, baseChangePointsEquiv_torus A i tb,
      ht, ht']
    simpa only [MonObj.comp_mul, comp_rootPoint, Category.assoc] using
      congrArg (fun v => p ≫ v) hxy
  have hh := hlaw Z' (p.left.appTop y) (p.left.appTop y')
    (p.left.appTop x) (p.left.appTop x') (p.left.appTop z) ta tb hrel
  have hh' := congrArg (GroupScheme.baseChangePointsEquiv b Q Z') hh
  rw [baseChangePointsEquiv_torus, baseChangePointsEquiv_torus, ht, ht'] at hh'
  apply (Over.pullback b).map_injective
  apply (GroupScheme.baseChangePointsEquiv b Q Z').injective
  rw [point_pullback, point_pullback]
  exact hh'

/-- Killing a fixed-exponent cocharacter is preserved in the standard
  split-torus coordinates after every scalar base change. -/
theorem cocharPoint_trivial_baseChange
    (q : splitTorus (Spec (CommRingCat.of R)) I ⟶ Q) (nu : I → ℤ)
    (hq : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Z ⟶ (Gm _).X),
      (c ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I nu)).hom.hom) ≫ q.hom.hom = 1)
    (A : Type u) [CommRing A] [Algebra R A]
    (Z : Over (Spec (CommRingCat.of A))) (c : Z ⟶ (Gm _).X) :
    (c ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I nu)).hom.hom) ≫
      (splitTorus.baseChangeHom (K := A) Q I q).hom.hom = 1 := by
  let b := algebraBaseMap R A
  have hc := LocalRootGroup.baseChangeCocharacter_groupHom_comp b nu q
  change Dynamic.baseChangeCocharacter b
    (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I nu) ≫ q) =
    CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫
      splitTorus.baseChangeHom (K := A) Q I q at hc
  apply (GroupScheme.baseChangePointsEquiv b Q Z).injective
  rw [map_one]
  change GroupScheme.baseChangePointsEquiv b Q Z
    (c ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I nu) ≫
        splitTorus.baseChangeHom (K := A) Q I q).hom.hom) = 1
  rw [← hc, Dynamic.baseChangePointsEquiv_baseChangeCocharacter,
    Grp.comp_hom_hom, ← Category.assoc]
  exact hq _ _

end Langlands.GroupScheme.LocalSplitCell


namespace Langlands.GroupScheme.splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G Q : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
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
  (q : splitTorus (Spec (CommRingCat.of R)) I ⟶ Q)
  (hq : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Z ⟶ (Gm _).X),
    (c ≫ (CommGroupScheme.groupHom
      (exponentCocharacter _ I (P.coroot a))).hom.hom) ≫ q.hom.hom = 1)

include hG hmax hP hmu hq in
/-- The actual rank-one centralizer satisfies the coroot-trivial torus
  quotient law over every test, by faithful etale descent of its Weyl data. -/
theorem rankOneQuotientLaw (hi : IsClosedSubgroup i) :
    RankOneQuotientLaw (torusHom I G i mu)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))
      (rootLift i mu hp ha) q := by
  let C := groupScheme I G i mu
  let p := pointedEtaleUnitCellReflection i mu hG hmax hP a ha hmu hp hm hi
    (IsLocalRing.closedPoint R)
  let E := p.affineEtaleUnitCell
  let := E.coefficientAlgebra
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let b := algebraBaseMap R E.ring
  let qa := splitTorus.baseChangeHom (K := E.ring) Q I q
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
  let : IsAffineHom ((GroupScheme.baseChange b).obj Q).X.hom :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd Q.X.hom b))
  let : IsAffine ((GroupScheme.baseChange b).obj Q).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj Q).X.hom
  apply RankOneQuotientLaw.of_faithfulBaseChange
    (torusHom I G i mu) _ _ q E.ring
  intro Z y y' x x' z t t' hxy
  have hkill : ∀ (Z : Over (Spec (CommRingCat.of E.ring))) (c : Γ(Z.left, ⊤)ˣ),
      W.tH c ≫ qa.hom.hom = 1 := by
    intro Z c
    change ((Gm.pointsEquiv _ Z).symm c ≫
      (CommGroupScheme.groupHom
        (exponentCocharacter _ I (P.coroot a))).hom.hom) ≫ qa.hom.hom = 1
    exact cocharPoint_trivial_baseChange q (P.coroot a) hq E.ring Z _
  have hrel : W.cellPt y t x * W.B z = W.cellPt y' t' x' := by
    change (rootPoint W.xm Z y * (t ≫ W.i.hom.hom) * rootPoint W.xp Z x) *
      rootPoint W.xm Z z =
        rootPoint W.xm Z y' * (t' ≫ W.i.hom.hom) * rootPoint W.xp Z x' at hxy
    simpa only [RingRootCell.CellData.cellPt, RingRootCell.CellData.A,
      RingRootCell.CellData.B, RingRootCell.CellData.I, rootPoint, mul_assoc] using hxy
  exact W.torus_quotient_eq_of_cellPt_relation qa hkill y y' x x' z t t' hrel

end Langlands.GroupScheme.splitTorus.RelativeCocharacterCentralizer

namespace Langlands.GroupScheme.LocalSplitCell

open splitTorus.RelativeCocharacterCentralizer

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G Q : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)
  (q : splitTorus (Spec (CommRingCat.of R)) I ⟶ Q)
  (hq : ∀ (Z : Over (Spec (CommRingCat.of R))) (c : Z ⟶ (Gm _).X),
    (c ≫ (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I (P.coroot a))).hom.hom) ≫ q.hom.hom = 1)

include hG hi hmax hP hp hm hq in
/-- Every actual opposite-root pair over a local reductive base satisfies
  the quotient law for any affine torus target map killing its coroot. -/
theorem rankOneQuotientLaw_of_reductive : RankOneQuotientLaw i xm xp q := by
  classical
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ :=
    LocalRootGroup.exists_kernel_exponent P (IsLocalRing.ResidueField R) a
  have hc := rankOneQuotientLaw i mu hG hmax hP a ha hmu hp hm q hq hi
  intro Z y y' x x' z t t' hxy
  apply hc Z y y' x x' z t t'
  let j := inclusion I G i mu
  let : IsClosedImmersion j.hom.hom.left := isClosedSubgroup_inclusion I G i mu
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono j.hom.hom).mp
  dsimp only [j]
  simpa only [MonObj.mul_comp, ← rootPoint_comp, Category.assoc,
    ← Grp.comp_hom_hom, rootLift_comp, torusHom_comp] using hxy

include hG hi hmax hP hp hm in
/-- In particular the actual all-coroot quotient preserves the torus
  coordinate of every opposite-root cell relation over every scheme test. -/
theorem rankOneQuotientLaw_corootProjection :
    RankOneQuotientLaw i xm xp
      (RelativeDerived.corootProjection (CommRingCat.of R) P) := by
  apply rankOneQuotientLaw_of_reductive hG i hi hmax hP a hp hm
  intro Z c
  exact RelativeDerived.corootProjection_coroot_points (CommRingCat.of R) P
    (hP.pairing (IsLocalRing.ResidueField R)) a Z c

end Langlands.GroupScheme.LocalSplitCell
