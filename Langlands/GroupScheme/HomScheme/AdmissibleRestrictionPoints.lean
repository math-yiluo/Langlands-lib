import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.SubgroupFunctor.ZariskiDescent

/-! # Actual points under restriction of admissible subgroup families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S} {M T : Over S}

/-- The point adjunction for direct family restriction, including the actual
comparison from the direct ambient pullback to the iterated pullback. -/
def familyPointsEquiv (a : T ⟶ M) (V : Over T.left) :
    (V ⟶ ((baseChange T.hom).obj G).X) ≃*
      ((Over.map a.left).obj V ⟶ ((baseChange M.hom).obj G).X) :=
  (isoPointsEquiv
    (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).symm V).trans
      (baseChangePointsEquiv a.left ((baseChange M.hom).obj G) V)

/-- The family point adjunction keeps the projection to the original group. -/
@[reassoc]
theorem familyPointsEquiv_original (a : T ⟶ M) (V : Over T.left)
    (x : V ⟶ ((baseChange T.hom).obj G).X) :
    (familyPointsEquiv (G := G) a V x).left ≫ pullback.fst G.X.hom M.hom =
      x.left ≫ pullback.fst G.X.hom T.hom := by
  simp only [familyPointsEquiv, MulEquiv.trans_apply, isoPointsEquiv_apply,
    Iso.symm_hom, baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_inv_fst]

/-- A subgroup restriction is the pullback of its all-test condition along
the family point adjunction. -/
theorem restrict_val_eq (a : T ⟶ M)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G)) :
    (restrict a F).val =
      (F.val.baseChange a.left).comap
        (Descent.pullbackComparison M.hom a.left T.hom (Over.w a) G).inv := by
  simp only [restrict, evaluate, familyHom, SubgroupFunctor.range_comp_iso,
    SubgroupFunctor.range_baseChangeHom, (admissibleRepresentative F).represents.2]

/-- Membership after restriction has its literal relative-test meaning. -/
theorem mem_restrict_iff (a : T ⟶ M)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G))
    (V : Over T.left) (x : V ⟶ ((baseChange T.hom).obj G).X) :
    x ∈ (restrict a F).val.carrier V ↔
      familyPointsEquiv (G := G) a V x ∈
        F.val.carrier ((Over.map a.left).obj V) := by
  rw [restrict_val_eq]
  rfl

/-- Family restriction is natural on arbitrary relative test schemes. -/
theorem familyPointsEquiv_naturality (a : T ⟶ M)
    {V W : Over T.left} (b : V ⟶ W)
    (x : W ⟶ ((baseChange T.hom).obj G).X) :
    familyPointsEquiv (G := G) a V (b ≫ x) =
      (Over.map a.left).map b ≫ familyPointsEquiv (G := G) a W x := by
  simp only [familyPointsEquiv, MulEquiv.trans_apply, isoPointsEquiv_apply,
    Iso.symm_hom, Category.assoc, baseChangePointsEquiv_naturality]

/-- A comparison of relative tests identifies family points whenever their
projections to the original group agree. -/
theorem familyPointsEquiv_eq_of_original (a : T ⟶ M)
    (V : Over T.left) (W : Over M.left)
    (b : (Over.map a.left).obj V ⟶ W)
    (x : V ⟶ ((baseChange T.hom).obj G).X)
    (y : W ⟶ ((baseChange M.hom).obj G).X)
    (h : x.left ≫ pullback.fst G.X.hom T.hom =
      b.left ≫ y.left ≫ pullback.fst G.X.hom M.hom) :
    familyPointsEquiv (G := G) a V x = b ≫ y := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Over.comp_left, Category.assoc,
      familyPointsEquiv_original] using h
  · exact (Over.w (familyPointsEquiv (G := G) a V x)).trans (Over.w (b ≫ y)).symm

/-- Membership transfers along an arbitrary comparison of relative tests
whose original group-valued points agree. -/
theorem mem_restrict_of_original (a : T ⟶ M)
    (F : AdmissibleSubgroup ((baseChange M.hom).obj G))
    (V : Over T.left) (W : Over M.left)
    (b : (Over.map a.left).obj V ⟶ W)
    (x : V ⟶ ((baseChange T.hom).obj G).X)
    (y : W ⟶ ((baseChange M.hom).obj G).X)
    (h : x.left ≫ pullback.fst G.X.hom T.hom =
      b.left ≫ y.left ≫ pullback.fst G.X.hom M.hom)
    (hy : y ∈ F.val.carrier W) :
    x ∈ (restrict a F).val.carrier V := by
  rw [mem_restrict_iff, familyPointsEquiv_eq_of_original a V W b x y h]
  exact F.val.comp_mem b hy

end Langlands.GroupScheme.TorusSubgroupModuli
