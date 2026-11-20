import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.GroupScheme.Torus.OrderedProjectorSubgroup
import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartAffineTestsProof

/-! # Base change of the ordered projector charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

open TorusSubgroupModuli (familyPointsEquiv familyPointsEquiv_original)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {T T' : Over S} (a : T' ⟶ T) (V : Over T'.left)

/-- The two structures over the original base agree on the underlying test scheme. -/
def baseTestComparison :
    (Over.map T.hom).obj ((Over.map a.left).obj V) ⟶ (Over.map T'.hom).obj V :=
  Over.homMk (𝟙 V.left) (by
    change 𝟙 V.left ≫ (V.hom ≫ T'.hom) = (V.hom ≫ a.left) ≫ T.hom
    rw [Category.id_comp, Category.assoc, Over.w a])

private theorem originalPoint {G : GroupScheme S} (x : V ⟶ ((baseChange T'.hom).obj G).X) :
    baseChangePointsEquiv T.hom G ((Over.map a.left).obj V) (familyPointsEquiv a V x) =
      baseTestComparison a V ≫ baseChangePointsEquiv T'.hom G V x := by
  apply Over.OverMorphism.ext
  simp only [baseChangePointsEquiv_left, Over.comp_left, baseTestComparison, Over.homMk_left]
  exact familyPointsEquiv_original a V x

private theorem familyPointsEquiv_pullHom {G H : GroupScheme S}
    (j : (baseChange T.hom).obj G ⟶ (baseChange T.hom).obj H)
    (x : V ⟶ ((baseChange T'.hom).obj G).X) :
    familyPointsEquiv a V (x ≫ (Descent.pullHom a.left (Over.w a) (Over.w a) j).hom.hom) =
      familyPointsEquiv a V x ≫ j.hom.hom :=
  Langlands.GroupScheme.HomScheme.familyPointsEquiv_comp_evaluate a j V x

section Projectors

variable {R : CommRingCat.{u}} {M M' : Over (Spec R)} (b : M' ⟶ M) (U : Over M'.left)
variable {J n : Type} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]
variable {Λ : Type u} [AddCommGroup Λ] (w : J → Λ)

private theorem sourcePoints_familyPointsEquiv
    (x : U ⟶ ((baseChange M'.hom).obj (Diagonalizable.groupScheme R Λ).toGrp).X) (m : Λ) :
    sourcePoints M Λ ((Over.map b.left).obj U) (familyPointsEquiv b U x) (.ofAdd m) =
      sourcePoints M' Λ U x (.ofAdd m) := by
  simp only [sourcePoints, MulEquiv.trans_apply, originalPoint]
  have h := Diagonalizable.characterPointsEquiv_naturality R Λ (baseTestComparison b U)
    (baseChangePointsEquiv M'.hom (Diagonalizable.groupScheme R Λ).toGrp U x) m
  refine h.trans ?_
  apply Units.ext
  change (𝟙 U.left : U.left ⟶ U.left).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

private theorem targetPoints_familyPointsEquiv
    (x : U ⟶ ((baseChange M'.hom).obj (GeneralLinear.groupScheme n R)).X) :
    targetPoints M n ((Over.map b.left).obj U) (familyPointsEquiv b U x) =
      targetPoints M' n U x := by
  simp only [targetPoints, MulEquiv.trans_apply, originalPoint]
  have h := GeneralLinear.pointsEquiv_naturality (baseTestComparison b U)
    (baseChangePointsEquiv M'.hom (GeneralLinear.groupScheme n R) U x)
  refine h.trans ?_
  apply Units.ext
  ext j k
  change (𝟙 U.left : U.left ⟶ U.left).appTop _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

/-- Pulling a projector subgroup back to a new base applies the function map to its projectors. -/
theorem pullHom_subgroupHom (P : Family J n Γ(M.left, ⊤)) :
    Descent.pullHom b.left (Over.w b) (Over.w b) (subgroupHom w M P) =
      subgroupHom w M' (P.map b.left.appTop.hom) := by
  refine hom_ext_points fun U x => (targetPoints M' n U).injective ?_
  rw [← targetPoints_familyPointsEquiv b U (x ≫ _), familyPointsEquiv_pullHom,
    targetPoints_subgroupHom, targetPoints_subgroupHom, map_appTop_comp]
  congr 1
  funext i
  exact sourcePoints_familyPointsEquiv b U x (w i)

/-- Restricting the chart family yields the projector subgroup classified by the test point. -/
theorem evaluate_chartFamily (x : M' ⟶ scheme J n R) :
    TorusSubgroupModuli.evaluate (chartFamily (n := n) (R := R) w) x =
      SubgroupFunctor.range (subgroupHom w M' (pointsEquiv J n R M' x)) := by
  let C := scheme J n R
  let P := pointsEquiv J n R C (𝟙 C)
  let D := (Diagonalizable.groupScheme R Λ).toGrp
  let e := Descent.pullbackComparison C.hom x.left M'.hom (Over.w x) D
  have h := pullHom_subgroupHom x w P
  have hfamily : TorusSubgroupModuli.familyHom (chartFamily (n := n) (R := R) w) x =
      e.hom ≫ subgroupHom w M' (P.map x.left.appTop.hom) := by
    rw [← h]
    rw [Descent.pullHom, ← Category.assoc]
    change _ = (e.hom ≫ e.inv) ≫ _
    rw [Iso.hom_inv_id, Category.id_comp]
    rfl
  have hx := pointsEquiv_naturality J n R x (𝟙 C)
  rw [Category.comp_id] at hx
  rw [TorusSubgroupModuli.evaluate, hfamily, SubgroupFunctor.range_iso_comp, ← hx]

/-- The classifying map of the chart evaluates to the constructed projector subgroup. -/
theorem evaluate_comp_chartMap {K : GroupScheme M.left}
    (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R))
    (hu : TorusSubgroupModuli.IsUniversal j)
    (hw : AddSubgroup.closure (Set.range w) = ⊤)
    (hs : IsSplitTorus (Diagonalizable.groupScheme R Λ).toGrp)
    (x : M' ⟶ scheme J n R) :
    TorusSubgroupModuli.evaluate j (x ≫ chartMap w j hu hw hs) =
      SubgroupFunctor.range (subgroupHom w M' (pointsEquiv J n R M' x)) := by
  have h := TorusSubgroupModuli.evaluate_eq_comp j (chartFamily (n := n) (R := R) w)
    (chartMap w j hu hw hs) (𝟙 _)
    ((evaluate_chartMap w j hu hw hs).trans (TorusSubgroupModuli.evaluate_id _).symm) x
  rw [Category.comp_id, evaluate_chartFamily w x] at h
  exact h

end Projectors

end Langlands.GroupScheme.OrderedProjectorScheme
