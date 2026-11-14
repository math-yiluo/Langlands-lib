import Langlands.GroupScheme.RelativeLevi.ConjugatorDescent
import Langlands.GroupScheme.PointCentralizer

/-! # Range conjugators as conjugacy after base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S : Scheme.{u}} {P L L' U : GroupScheme S}

/-- The conjugate of a base-changed subgroup by a point over the new base. -/
def rangeConjugateAt (l : L ⟶ P) (T : Over S) (g : T ⟶ P.X) :
    SubgroupFunctor ((GroupScheme.baseChange T.hom).obj P) :=
  SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map l ≫
    (((GroupScheme.baseChange T.hom).obj P).innerIso
      ((baseChangeBasePointsEquiv T.hom P).symm g)).hom)

/-- Membership in this conjugate is the original range condition after
inverse conjugation by the restricted point. -/
theorem mem_rangeConjugateAt_iff (l : L ⟶ P) (T : Over S) (g : T ⟶ P.X)
    {V : Over T.left} (x : V ⟶ ((GroupScheme.baseChange T.hom).obj P).X) :
    x ∈ (rangeConjugateAt l T g).carrier V ↔
      (Over.homMk (U := (Over.map T.hom).obj V) (V := T) V.hom (by simp) ≫ g)⁻¹ *
        baseChangePointsEquiv T.hom P V x *
        (Over.homMk (U := (Over.map T.hom).obj V) (V := T) V.hom (by simp) ≫ g) ∈
          (SubgroupFunctor.range l).carrier ((Over.map T.hom).obj V) := by
  rw [rangeConjugateAt, MaximalTorusParameterExistence.mem_range_comp_innerIso_iff,
    SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
    map_mul, map_mul, map_inv, baseChangePointsEquiv_constantPoint_symm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The all-test conjugator predicate is equality of the corresponding
base-changed ranges over the domain of the point. -/
theorem isRangeConjugator_iff_range_baseChange_eq (l : L ⟶ P) (l' : L' ⟶ P)
    (T : Over S) (g : T ⟶ P.X) :
    IsRangeConjugator l l' g ↔
      SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map l') =
        rangeConjugateAt l T g := by
  constructor
  · intro hg
    ext V x
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
      mem_rangeConjugateAt_iff]
    exact hg ((Over.map T.hom).obj V)
      (Over.homMk (U := (Over.map T.hom).obj V) (V := T) V.hom (by simp))
      (baseChangePointsEquiv T.hom P V x)
  · intro hg V a x
    let W : Over T.left := Over.mk a.left
    let e : (Over.map T.hom).obj W ≅ V :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ V.hom = a.left ≫ T.hom
        simpa only [Category.id_comp] using (Over.w a).symm)
    let c : (Over.map T.hom).obj W ⟶ T := Over.homMk W.hom (by simp)
    have hc : c = e.hom ≫ a := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp _).symm
    have transport (F : SubgroupFunctor P) (z : V ⟶ P.X) :
        e.hom ≫ z ∈ F.carrier _ ↔ z ∈ F.carrier V := by
      constructor
      · intro hz
        simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv hz
      · exact F.comp_mem e.hom
    let y := (baseChangePointsEquiv T.hom P W).symm (e.hom ≫ x)
    have hy : y ∈ (SubgroupFunctor.range ((GroupScheme.baseChange T.hom).map l')).carrier W ↔
        y ∈ (rangeConjugateAt l T g).carrier W := by rw [hg]
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.mem_baseChange,
      mem_rangeConjugateAt_iff] at hy
    change baseChangePointsEquiv T.hom P W
        ((baseChangePointsEquiv T.hom P W).symm (e.hom ≫ x)) ∈ _ ↔
      (c ≫ g)⁻¹ *
          baseChangePointsEquiv T.hom P W
            ((baseChangePointsEquiv T.hom P W).symm (e.hom ≫ x)) *
          (c ≫ g) ∈ _ at hy
    rw [MulEquiv.apply_symm_apply, hc, Category.assoc] at hy
    have hm : (e.hom ≫ (a ≫ g))⁻¹ * (e.hom ≫ x) * (e.hom ≫ (a ≫ g)) =
        e.hom ≫ ((a ≫ g)⁻¹ * x * (a ≫ g)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    rw [hm, transport, transport] at hy
    exact hy

end Langlands.GroupScheme.RelativeLevi
