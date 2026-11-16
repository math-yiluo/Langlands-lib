import Langlands.GroupScheme.Reductive.LocalRankOneSuppliedWeylData
import Langlands.GroupScheme.Reductive.RankOneRingSuppliedLaws

/-! # Rank-one laws for actual supplied opposite roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Rank-one identities are preserved by a homomorphism of ambient groups. -/
theorem RankOneLaws.comp
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {nu : I → ℤ} {xp xm : Ga R ⟶ G}
    (h : RankOneLaws i nu xp xm) (f : G ⟶ H) :
    RankOneLaws (i ≫ f) nu (xp ≫ f) (xm ≫ f) := by
  have hn (Z : Over (Spec (CommRingCat.of R))) :
      H.constantPoint (weylPoint (xp ≫ f) (xm ≫ f)) Z =
        G.constantPoint (weylPoint xp xm) Z ≫ f.hom.hom := by
    rw [weylPoint_comp]
    simp only [GroupScheme.constantPoint, Category.assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z x
    have e := congrArg (fun g => g ≫ f.hom.hom) (h.1 Z x)
    simpa only [hn, rootPoint_comp, MonObj.mul_comp, GrpObj.inv_comp] using e
  · intro Z x
    have e := congrArg (fun g => g ≫ f.hom.hom) (h.2.1 Z x)
    simpa only [hn, rootPoint_comp, MonObj.mul_comp, GrpObj.inv_comp] using e
  · intro Z
    have e := congrArg (fun g => g ≫ f.hom.hom) (h.2.2.1 Z)
    simpa only [hn, MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc] using e
  · intro Z x y d hd
    have e := congrArg (fun g => g ≫ f.hom.hom) (h.2.2.2 Z x y d hd)
    simpa only [rootPoint_comp, MonObj.mul_comp, Grp.comp_hom_hom,
      Category.assoc] using e

end LocalSplitCell

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange

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

include hG hmax hP hmu in
/-- The four laws for lifted supplied roots descend from the pointed etale
cell over the closed residue point. -/
theorem rankOneLaws_rootLift (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    RankOneLaws (torusHom I G i mu) (P.coroot a)
      (rootLift i mu hp ha)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha)) := by
  let p := pointedEtaleUnitCellReflection i mu hG hmax hP a ha hmu hp hm hi
    (IsLocalRing.closedPoint R)
  let E := p.affineEtaleUnitCell
  let := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let W := affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi
  let b := algebraBaseMap R E.ring
  let : Etale (algebraBaseMap R E.ring) := by
    rw [E.coefficientAlgebra_baseMap]
    exact E.etale
  let : Surjective (algebraBaseMap R E.ring) := by
    rw [E.coefficientAlgebra_baseMap]
    exact ⟨E.projection_surjective⟩
  let : IsAffineHom W.G.X.hom := by
    change IsAffineHom (((GroupScheme.baseChange b).obj C).X.hom)
    exact inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
  let : IsAffine W.G.X.left := isAffine_of_isAffineHom W.G.X.hom
  apply RankOneLaws.of_baseChange E.ring
  have hb : W.cβ = 1 :=
    affineEtaleWeylData_beta_eq_one i mu hG hmax hP a ha hmu hp hm E hi hn
  have h := W.rankOneLaws_of_beta_eq_one (𝟙 _) (P.coroot a)
    (by exact Category.comp_id _) hb
  change RankOneLaws W.i (P.coroot a) W.xp W.xm at h
  exact h

include mu hG hmax hP ha hmu hp hm in
/-- Including the actual rank-one centralizer gives the same laws in the
original ambient reductive group. -/
theorem rankOneLaws_of_isolating_cocharacter (hi : IsClosedSubgroup i)
    (hn : IsWeylPoint i (weylPoint xp xm) (P.reflection a)) :
    RankOneLaws i (P.coroot a) xp xm := by
  have h := (rankOneLaws_rootLift i mu hG hmax hP a ha hmu hp hm hi hn).comp
    (inclusion I G i mu)
  simpa only [torusHom_comp, rootLift_comp] using h

end splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell

/-- Every supplied opposite root pair whose Weyl product acts by its root
reflection satisfies the four rank-one laws over a local ring. -/
def LocalSplitRootPairLawsStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom],
    IsReductive G →
    ∀ (I : Type u) [Fintype I] [DecidableEq I]
      (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
      IsClosedSubgroup i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      ∀ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
        IsFibrewiseRootDatumOf I G i P →
        ∀ (a : J) (xp xm : Ga R ⟶ G),
          IsRootParametrization i (P.root a) xp →
          IsRootParametrization i (-P.root a) xm →
          IsWeylPoint i (weylPoint xp xm) (P.reflection a) →
          RankOneLaws i (P.coroot a) xp xm

/-- The isolating cocharacter exists for every root of the fibrewise reduced
root datum, so the supplied-root laws have no extra cocharacter hypothesis. -/
theorem localSplitRootPairLaws : LocalSplitRootPairLawsStatement.{u} := by
  intro R _ _ G _ hG I _ _ i hi hmax J P hP a xp xm hp hm hn
  have : Finite J := hP.finite
  have := hP.isReduced
  obtain ⟨mu, ha, hmu⟩ :=
    LocalRootGroup.exists_kernel_exponent P (IsLocalRing.ResidueField R) a
  exact splitTorus.RelativeCocharacterCentralizer.rankOneLaws_of_isolating_cocharacter
    i mu hG hmax hP a ha hmu hp hm hi hn

end Langlands.GroupScheme
