import Langlands.GroupScheme.RelativeLevi.LocalConjugacyReduction

/-! # Refining covers carrying all-test conjugators -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeLevi

variable {S S' : Scheme.{u}} {P L L' : GroupScheme S}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Projection of actual pullback points identifies the all-test conjugator
predicate over the new base with that over the original base. -/
theorem isRangeConjugator_baseChange_iff
    (b : S' ⟶ S) (l : L ⟶ P) (l' : L' ⟶ P) (T : Over S')
    (g : T ⟶ ((GroupScheme.baseChange b).obj P).X) :
    IsRangeConjugator ((GroupScheme.baseChange b).map l)
        ((GroupScheme.baseChange b).map l') g ↔
      IsRangeConjugator l l' (baseChangePointsEquiv b P T g) := by
  constructor
  · intro hg V a y
    let W : Over S' := Over.mk (a.left ≫ T.hom)
    let c : W ⟶ T := Over.homMk a.left rfl
    let e : (Over.map b).obj W ≅ V :=
      Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ V.hom = (a.left ≫ T.hom) ≫ b
        have ha : a.left ≫ (T.hom ≫ b) = V.hom := Over.w a
        simpa only [Category.id_comp, Category.assoc] using ha.symm)
    have hc : (Over.map b).map c = e.hom ≫ a := by
      apply Over.OverMorphism.ext
      exact (Category.id_comp a.left).symm
    have transport (F : SubgroupFunctor P) (x : V ⟶ P.X) :
        e.hom ≫ x ∈ F.carrier _ ↔ x ∈ F.carrier V := by
      constructor
      · intro hx
        simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv hx
      · exact F.comp_mem e.hom
    let z := (baseChangePointsEquiv b P W).symm (e.hom ≫ y)
    have h := hg W c z
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_baseChange,
      map_mul, map_mul, map_inv, baseChangePointsEquiv_naturality] at h
    have hz : baseChangePointsEquiv b P W z = e.hom ≫ y :=
      (baseChangePointsEquiv b P W).apply_symm_apply _
    rw [hz] at h
    change e.hom ≫ y ∈ (SubgroupFunctor.range l').carrier _ ↔
      ((Over.map b).map c ≫ baseChangePointsEquiv b P T g)⁻¹ *
          (e.hom ≫ y) *
          ((Over.map b).map c ≫ baseChangePointsEquiv b P T g) ∈
        (SubgroupFunctor.range l).carrier _ at h
    rw [hc, Category.assoc] at h
    have hm :
        (e.hom ≫ (a ≫ baseChangePointsEquiv b P T g))⁻¹ * (e.hom ≫ y) *
            (e.hom ≫ (a ≫ baseChangePointsEquiv b P T g)) =
          e.hom ≫ ((a ≫ baseChangePointsEquiv b P T g)⁻¹ * y *
            (a ≫ baseChangePointsEquiv b P T g)) := by
      rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    rw [hm, transport, transport] at h
    exact h
  · intro hg V a y
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.mem_baseChange, SubgroupFunctor.mem_baseChange,
      map_mul, map_mul, map_inv, baseChangePointsEquiv_naturality]
    exact hg ((Over.map b).obj V) ((Over.map b).map a) (baseChangePointsEquiv b P V y)

/-- The actual pullback-point equivalence restricts to conjugator points. -/
def rangeConjugatorPointsEquiv (b : S' ⟶ S) (l : L ⟶ P) (l' : L' ⟶ P)
    (T : Over S') :
    {g : T ⟶ ((GroupScheme.baseChange b).obj P).X //
        IsRangeConjugator ((GroupScheme.baseChange b).map l)
          ((GroupScheme.baseChange b).map l') g} ≃
      {g : (Over.map b).obj T ⟶ P.X // IsRangeConjugator l l' g} where
  toFun g := ⟨baseChangePointsEquiv b P T g.1,
    (isRangeConjugator_baseChange_iff b l l' T g.1).mp g.2⟩
  invFun g := ⟨(baseChangePointsEquiv b P T).symm g.1,
    (isRangeConjugator_baseChange_iff b l l' T _).mpr (by
      simpa only [MulEquiv.apply_symm_apply] using g.2)⟩
  left_inv g := Subtype.ext ((baseChangePointsEquiv b P T).symm_apply_apply g.1)
  right_inv g := Subtype.ext ((baseChangePointsEquiv b P T).apply_symm_apply g.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Etale-local conjugators over a new base project to etale-local conjugators
over the original base. -/
theorem etaleLocallyRangeConjugate_of_baseChange
    (b : S' ⟶ S) (l : L ⟶ P) (l' : L' ⟶ P) (T : Over S')
    (h : EtaleLocallyRangeConjugate.{u, v}
      ((GroupScheme.baseChange b).map l) ((GroupScheme.baseChange b).map l') T) :
    EtaleLocallyRangeConjugate.{u, v} l l' ((Over.map b).obj T) := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine ⟨𝒰, fun k => ?_⟩
  obtain ⟨g, hg⟩ := h𝒰 k
  let V := SubgroupFunctor.etaleCoverObj (T := T) 𝒰 k
  let a : SubgroupFunctor.etaleCoverObj (T := (Over.map b).obj T) 𝒰 k ⟶
      (Over.map b).obj V :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ ((𝒰.f k ≫ T.hom) ≫ b) = 𝒰.f k ≫ (T.hom ≫ b)
      simp only [Category.id_comp, Category.assoc])
  exact ⟨a ≫ baseChangePointsEquiv b P V g,
    ((isRangeConjugator_baseChange_iff b l l' V g).mp hg).comp a⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the covers witnessing local existence preserves the all-test
conjugator predicate. -/
theorem etaleLocallyRangeConjugate_of_cover
    (l : L ⟶ P) (l' : L' ⟶ P) (T : Over S)
    (𝒰 : T.left.Cover.{v} (Scheme.precoverage @Etale))
    (h : ∀ k, EtaleLocallyRangeConjugate.{u, w} l l'
      (SubgroupFunctor.etaleCoverObj (T := T) 𝒰 k)) :
    EtaleLocallyRangeConjugate.{u, max v w} l l' T := by
  let : Scheme.IsJointlySurjectivePreserving (@Etale.{u}) :=
    Scheme.isJointlySurjectivePreserving _
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun k => ?_⟩
  obtain ⟨g, hg⟩ := h𝒱 k.1 k.2
  let a : SubgroupFunctor.etaleCoverObj (T := T) (𝒰.bind 𝒱) k ⟶
      SubgroupFunctor.etaleCoverObj
        (T := SubgroupFunctor.etaleCoverObj (T := T) 𝒰 k.1) (𝒱 k.1) k.2 :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ ((𝒱 k.1).f k.2 ≫ (𝒰.f k.1 ≫ T.hom)) =
        ((𝒱 k.1).f k.2 ≫ 𝒰.f k.1) ≫ T.hom
      simp only [Category.id_comp, Category.assoc])
  exact ⟨a ≫ g, hg.comp a⟩

end Langlands.GroupScheme.RelativeLevi
