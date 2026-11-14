import Langlands.GroupScheme.RelativeLevi.ParabolicMatching
import Langlands.GroupScheme.HomScheme.ChartCoverTransport

/-! # Canonical base change of the actual parabolic presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open TorusSubgroupModuli

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- An ambient group isomorphism identifies actual parabolic subgroup functors. -/
def ambientEquiv {B : Scheme.{u}} {H J : GroupScheme B} (e : H ≅ J) :
    ParabolicSubgroup H ≃ ParabolicSubgroup J where
  toFun F := ⟨F.val.comap e.inv, isParabolic_comapIso F e.symm⟩
  invFun F := ⟨F.val.comap e.hom, isParabolic_comapIso F e⟩
  left_inv F := by
    apply Subtype.ext
    change (F.val.comap e.inv).comap e.hom = F.val
    rw [← SubgroupFunctor.comap_comp, e.hom_inv_id, SubgroupFunctor.comap_id]
  right_inv F := by
    apply Subtype.ext
    change (F.val.comap e.hom).comap e.inv = F.val
    rw [← SubgroupFunctor.comap_comp, e.inv_hom_id, SubgroupFunctor.comap_id]

/-- The canonical direct/iterated pullback comparison on actual parabolic families. -/
def baseChangeEquiv (b : S' ⟶ S) (T : Over S') :
    ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj
      ((GroupScheme.baseChange b).obj G)) ≃
      ParabolicSubgroup ((GroupScheme.baseChange ((Over.map b).obj T).hom).obj G) :=
  ambientEquiv (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl G)

/-- On all-test subgroup functors, the comparison is inverse-image along the
inverse of the canonical ambient isomorphism. -/
theorem baseChangeEquiv_val (b : S' ⟶ S) (T : Over S')
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj
      ((GroupScheme.baseChange b).obj G))) :
    (baseChangeEquiv b T F).val = F.val.comap
      (Descent.pullbackComparison b T.hom (T.hom ≫ b) rfl G).inv := rfl

/-- The comparison sends the range of any actual representative to the range
of the same inclusion followed by the canonical ambient comparison. -/
theorem baseChangeEquiv_range (b : S' ⟶ S) {T : Over S'}
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj
      ((GroupScheme.baseChange b).obj G)))
    {P : GroupScheme T.left}
    (j : P ⟶ (GroupScheme.baseChange T.hom).obj ((GroupScheme.baseChange b).obj G))
    (hj : SubgroupFunctor.range j = F.val) :
    (baseChangeEquiv b T F).val = SubgroupFunctor.range (pushFamily b j) := by
  rw [baseChangeEquiv_val, pushFamily, SubgroupFunctor.range_comp_iso, hj]

/-- The direct/iterated comparison commutes with actual family restriction. -/
theorem restrict_baseChangeEquiv (b : S' ⟶ S) (hG : IsReductive G)
    {T M : Over S'} (a : T ⟶ M)
    (F : ParabolicSubgroup ((GroupScheme.baseChange M.hom).obj
      ((GroupScheme.baseChange b).obj G))) :
    restrict hG ((Over.map b).map a) (baseChangeEquiv b M F) =
      baseChangeEquiv b T (restrict (hG.baseChange b) a F) := by
  apply Subtype.ext
  let r := parabolicRepresentative F
  rw [restrict_eq_evaluate hG _ (pushFamily b r.hom)
    (baseChangeEquiv_range b F r.hom r.represents.2).symm,
    baseChangeEquiv_range b (restrict (hG.baseChange b) a F)
      (familyHom r.hom a) rfl]
  exact congrArg SubgroupFunctor.range (familyHom_pushFamily b r.hom a)

/-- Arbitrary change of base of the group agrees naturally with restriction
of its actual parabolic presheaf along the map of slice categories. -/
def parabolicPresheafBaseChangeIso (b : S' ⟶ S) (hG : IsReductive G) :
    parabolicPresheaf ((GroupScheme.baseChange b).obj G) (hG.baseChange b) ≅
      (Over.map b).op ⋙ parabolicPresheaf G hG :=
  NatIso.ofComponents (fun T => (baseChangeEquiv b T.unop).toIso) (fun a => by
    apply TypeCat.homEquiv.injective
    funext F
    exact (restrict_baseChangeEquiv b hG a.unop F).symm)

end Langlands.GroupScheme.ParabolicSubgroupModuli
