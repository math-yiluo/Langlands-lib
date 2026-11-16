import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.Reductive.LocalSplitPositiveCell
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Rank-one laws on every scheme test and their descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Both root conjugations, the Weyl square, and the unit-denominator
rank-one relation, for an actual opposite pair on every scheme test. -/
def RankOneLaws (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (nu : I → ℤ) (xp xm : Ga R ⟶ G) : Prop :=
  (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    G.constantPoint (weylPoint xp xm) Z * rootPoint xp Z x *
      (G.constantPoint (weylPoint xp xm) Z)⁻¹ = rootPoint xm Z (-x)) ∧
  (∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
    G.constantPoint (weylPoint xp xm) Z * rootPoint xm Z x *
      (G.constantPoint (weylPoint xp xm) Z)⁻¹ = rootPoint xp Z (-x)) ∧
  (∀ (Z : Over (Spec (CommRingCat.of R))),
    G.constantPoint (weylPoint xp xm) Z * G.constantPoint (weylPoint xp xm) Z =
      cocharPoint nu Z (-1) ≫ i.hom.hom) ∧
  ∀ (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) (d : Γ(Z.left, ⊤)ˣ),
    (d : Γ(Z.left, ⊤)) = 1 + x * y →
    rootPoint xp Z x * rootPoint xm Z y =
      rootPoint xm Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * y) *
        (cocharPoint nu Z d ≫ i.hom.hom) *
        rootPoint xp Z ((↑d⁻¹ : Γ(Z.left, ⊤)) * x)

/-- Fixed-exponent cocharacter points commute with restriction of the test. -/
theorem comp_cocharPoint (nu : I → ℤ)
    {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z) (d : Γ(Z.left, ⊤)ˣ) :
    f ≫ cocharPoint nu Z d =
      cocharPoint nu W (Units.map f.left.appTop.hom.toMonoidHom d) := by
  apply (splitTorus.pointsEquiv I W).injective
  rw [splitTorus.pointsEquiv_naturality]
  simp only [cocharPoint, MulEquiv.apply_symm_apply]
  funext j
  exact map_zpow (Units.map f.left.appTop.hom.toMonoidHom) d (nu j)

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.LocalSplitRootBaseChange

open LocalSplitCell

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Standard cocharacter points retain their coordinates under base change. -/
theorem baseChangePointsEquiv_cocharPoint (nu : I → ℤ)
    (Z : Over (Spec (CommRingCat.of A))) (d : Γ(Z.left, ⊤)ˣ) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
      (cocharPoint nu Z d ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) =
      cocharPoint nu ((Over.map (algebraBaseMap R A)).obj Z) d := by
  apply (splitTorus.pointsEquiv I _).injective
  have h := splitTorus.pointsEquiv_baseChangeIso_hom (algebraBaseMap R A) I Z
    (cocharPoint nu Z d ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  simp only [cocharPoint, MulEquiv.apply_symm_apply] at h ⊢
  simp only [splitTorus.baseChangePointsEquiv, MulEquiv.trans_apply] at h
  convert h.symm using 1

/-- The constant family of the Weyl product retains the original coordinates. -/
theorem baseChangePointsEquiv_constantWeyl (xp xm : Ga R ⟶ G)
    (Z : Over (Spec (CommRingCat.of A))) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
      (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).constantPoint
        (weylPoint (baseChangeRoot A xp) (baseChangeRoot A xm)) Z) =
      G.constantPoint (weylPoint xp xm) ((Over.map (algebraBaseMap R A)).obj Z) := by
  simp only [constantPoint_weylPoint, map_mul, baseChangePointsEquiv_rootPoint]

end Langlands.GroupScheme.LocalSplitRootBaseChange

namespace Langlands.GroupScheme.LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Rank-one identities descend through a coefficient extension whose pullback
on scheme tests is faithful. -/
theorem RankOneLaws.of_baseChange
    (A : Type u) [CommRing A] [Algebra R A]
    [(Over.pullback (algebraBaseMap R A)).Faithful]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (nu : I → ℤ) (xp xm : Ga R ⟶ G)
    (h : RankOneLaws (splitTorus.baseChangeHom (K := A) G I i) nu
      (baseChangeRoot A xp) (baseChangeRoot A xm)) :
    RankOneLaws i nu xp xm := by
  let test (Z : Over (Spec (CommRingCat.of R))) :=
    (Over.pullback (algebraBaseMap R A)).obj Z
  let cover (Z : Over (Spec (CommRingCat.of R))) :
      (Over.map (algebraBaseMap R A)).obj (test Z) ⟶ Z :=
    (Over.mapPullbackAdj (algebraBaseMap R A)).counit.app Z
  have hcover (Z : Over (Spec (CommRingCat.of R))) : Epi (cover Z) :=
    inferInstanceAs (Epi ((Over.mapPullbackAdj (algebraBaseMap R A)).counit.app Z))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z x
    have := hcover Z
    apply (cancel_epi (cover Z)).1
    simp only [MonObj.comp_mul, GrpObj.comp_inv, G.constantPoint_naturality,
      comp_rootPoint, map_neg]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (test Z))
      (h.1 (test Z) ((cover Z).left.appTop x))
    simpa only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint] using e
  · intro Z x
    have := hcover Z
    apply (cancel_epi (cover Z)).1
    simp only [MonObj.comp_mul, GrpObj.comp_inv, G.constantPoint_naturality,
      comp_rootPoint, map_neg]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (test Z))
      (h.2.1 (test Z) ((cover Z).left.appTop x))
    simpa only [map_mul, map_inv, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_rootPoint] using e
  · intro Z
    have := hcover Z
    apply (cancel_epi (cover Z)).1
    have hminus : Units.map (cover Z).left.appTop.hom.toMonoidHom
        (-1 : Γ(Z.left, ⊤)ˣ) = -1 := by
      convert Units.map_neg_one (cover Z).left.appTop.hom using 1
      rfl
    simp only [MonObj.comp_mul, G.constantPoint_naturality, ← Category.assoc,
      comp_cocharPoint, hminus]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (test Z))
      (h.2.2.1 (test Z))
    simpa only [map_mul, baseChangePointsEquiv_constantWeyl,
      baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint] using e
  · intro Z x y d hd
    have := hcover Z
    apply (cancel_epi (cover Z)).1
    simp only [MonObj.comp_mul, comp_rootPoint, ← Category.assoc,
      comp_cocharPoint, map_mul]
    let res : Γ(Z.left, ⊤) →+* Γ((test Z).left, ⊤) :=
      (cover Z).left.appTop.hom
    let d' := Units.map res.toMonoidHom d
    have hd' : (d' : Γ((test Z).left, ⊤)) =
        1 + res x * res y := by
      change res (d : Γ(Z.left, ⊤)) = _
      rw [hd, map_add, map_one, map_mul]
    have e := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G (test Z))
      (h.2.2.2 (test Z) (res x) (res y) d' hd')
    simp only [map_mul, baseChangePointsEquiv_rootPoint,
      baseChangePointsEquiv_torus, baseChangePointsEquiv_cocharPoint,
      d', Units.coe_map_inv] at e
    convert e using 1

end Langlands.GroupScheme.LocalSplitCell
