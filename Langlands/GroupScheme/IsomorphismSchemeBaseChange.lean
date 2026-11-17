import Langlands.GroupScheme.IsomorphismScheme
import Mathlib.CategoryTheory.Yoneda

/-! # All-test group-isomorphism families under change of base -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S} {U : Over S'}

/-- Restrict an all-test isomorphism family to schemes over a new base. -/
def baseChangeFamily (e : LocalGroupIso G H ((Over.map b).obj U)) :
    LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U where
  toFun {T} a := (baseChangePointsEquiv b G T).trans
    ((e.toFun ((Over.map b).map a)).trans (baseChangePointsEquiv b H T).symm)
  naturality {T T'} t a g := by
    apply (baseChangePointsEquiv b H T').injective
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [baseChangePointsEquiv_naturality, baseChangePointsEquiv_naturality,
      MulEquiv.apply_symm_apply, Functor.map_comp, e.naturality]

@[simp] theorem baseChangeFamily_toFun (e : LocalGroupIso G H ((Over.map b).obj U))
    {T : Over S'} (a : T ⟶ U) (g : T ⟶ ((baseChange b).obj G).X) :
    baseChangePointsEquiv b H T ((e.baseChangeFamily b).toFun a g) =
      e.toFun ((Over.map b).map a) (baseChangePointsEquiv b G T g) :=
  (baseChangePointsEquiv b H T).apply_symm_apply _

namespace ChangeOfBase

/-- A test over the old base acquires a new-base structure from its parameter point. -/
def test {T : Over S} (a : T ⟶ (Over.map b).obj U) : Over S' :=
  Over.mk (a.left ≫ U.hom)

def testPoint {T : Over S} (a : T ⟶ (Over.map b).obj U) : test b a ⟶ U :=
  Over.homMk a.left rfl

def testMap {T T' : Over S} (t : T' ⟶ T) (a : T ⟶ (Over.map b).obj U) :
    test b (t ≫ a) ⟶ test b a :=
  Over.homMk t.left (by exact (Category.assoc _ _ _).symm)

@[simp] theorem testMap_testPoint {T T' : Over S} (t : T' ⟶ T)
    (a : T ⟶ (Over.map b).obj U) :
    testMap b t a ≫ testPoint b a = testPoint b (t ≫ a) := by
  apply Over.OverMorphism.ext
  rfl

def testIso {T : Over S} (a : T ⟶ (Over.map b).obj U) :
    (Over.map b).obj (test b a) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom = (a.left ≫ U.hom) ≫ b
    rw [Category.id_comp, Category.assoc]
    exact (Over.w a).symm)

private def precompPointsEquiv {T T' : Over S} (i : T ≅ T')
    (G : GroupScheme S) : (T ⟶ G.X) ≃* (T' ⟶ G.X) where
  toFun g := i.inv ≫ g
  invFun g := i.hom ≫ g
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := MonObj.comp_mul _ _ _

def pointsEquiv (G : GroupScheme S) {T : Over S}
    (a : T ⟶ (Over.map b).obj U) :
    (test b a ⟶ ((baseChange b).obj G).X) ≃* (T ⟶ G.X) :=
  (baseChangePointsEquiv b G (test b a)).trans (precompPointsEquiv (testIso b a) G)

@[simp] theorem pointsEquiv_left (G : GroupScheme S) {T : Over S}
    (a : T ⟶ (Over.map b).obj U) (x : test b a ⟶ ((baseChange b).obj G).X) :
    (pointsEquiv b G a x).left = x.left ≫ pullback.fst G.X.hom b := by
  change 𝟙 T.left ≫ (x.left ≫ pullback.fst G.X.hom b) = _
  exact Category.id_comp _

theorem pointsEquiv_naturality (G : GroupScheme S) {T T' : Over S}
    (t : T' ⟶ T) (a : T ⟶ (Over.map b).obj U)
    (x : test b a ⟶ ((baseChange b).obj G).X) :
    pointsEquiv b G (t ≫ a) (testMap b t a ≫ x) = t ≫ pointsEquiv b G a x := by
  apply Over.OverMorphism.ext
  simp only [pointsEquiv_left, Over.comp_left]
  change (t.left ≫ x.left) ≫ pullback.fst G.X.hom b =
    t.left ≫ (x.left ≫ pullback.fst G.X.hom b)
  exact Category.assoc _ _ _

theorem pointsEquiv_symm_naturality (G : GroupScheme S) {T T' : Over S}
    (t : T' ⟶ T) (a : T ⟶ (Over.map b).obj U) (g : T ⟶ G.X) :
    (pointsEquiv b G (t ≫ a)).symm (t ≫ g) =
      testMap b t a ≫ (pointsEquiv b G a).symm g := by
  apply (pointsEquiv b G (t ≫ a)).injective
  rw [MulEquiv.apply_symm_apply, pointsEquiv_naturality, MulEquiv.apply_symm_apply]

end ChangeOfBase

/-- Reinterpret an all-test family over the new base on old-base tests with a parameter point. -/
def fromBaseChangeFamily
    (e : LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U) :
    LocalGroupIso G H ((Over.map b).obj U) where
  toFun a := (ChangeOfBase.pointsEquiv b G a).symm.trans
    ((e.toFun (ChangeOfBase.testPoint b a)).trans (ChangeOfBase.pointsEquiv b H a))
  naturality t a g := by
    simp only [MulEquiv.trans_apply]
    rw [ChangeOfBase.pointsEquiv_symm_naturality,
      ← ChangeOfBase.testMap_testPoint, e.naturality, ChangeOfBase.pointsEquiv_naturality]

@[simp] theorem fromBaseChangeFamily_toFun
    (e : LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U)
    {T : Over S} (a : T ⟶ (Over.map b).obj U) (g : T ⟶ G.X) :
    (e.fromBaseChangeFamily b).toFun a g = ChangeOfBase.pointsEquiv b H a
      (e.toFun (ChangeOfBase.testPoint b a) ((ChangeOfBase.pointsEquiv b G a).symm g)) := rfl

@[simp] theorem fromBaseChangeFamily_baseChangeFamily
    (e : LocalGroupIso G H ((Over.map b).obj U)) :
    (e.baseChangeFamily b).fromBaseChangeFamily b = e := by
  apply ext_toFun
  intro T a g
  rw [fromBaseChangeFamily_toFun]
  change (ChangeOfBase.testIso b a).inv ≫
    baseChangePointsEquiv b H (ChangeOfBase.test b a)
      ((e.baseChangeFamily b).toFun (ChangeOfBase.testPoint b a)
        ((ChangeOfBase.pointsEquiv b G a).symm g)) = e.toFun a g
  rw [baseChangeFamily_toFun]
  have hg : baseChangePointsEquiv b G (ChangeOfBase.test b a)
      ((ChangeOfBase.pointsEquiv b G a).symm g) = (ChangeOfBase.testIso b a).hom ≫ g :=
    (baseChangePointsEquiv b G (ChangeOfBase.test b a)).apply_symm_apply _
  have ha : (Over.map b).map (ChangeOfBase.testPoint b a) =
      (ChangeOfBase.testIso b a).hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = 𝟙 T.left ≫ a.left
    exact (Category.id_comp _).symm
  rw [hg, ha, e.naturality]
  simp

@[simp] theorem baseChangeFamily_fromBaseChangeFamily
    (e : LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U) :
    (e.fromBaseChangeFamily b).baseChangeFamily b = e := by
  apply ext_toFun
  intro T a g
  let a₀ := (Over.map b).map a
  let j : ChangeOfBase.test b a₀ ≅ T := Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom = a.left ≫ U.hom
    rw [Category.id_comp]
    exact (Over.w a).symm)
  have ha : ChangeOfBase.testPoint b a₀ = j.hom ≫ a := by
    apply Over.OverMorphism.ext
    change a.left = 𝟙 T.left ≫ a.left
    exact (Category.id_comp _).symm
  have hg : (ChangeOfBase.pointsEquiv b G a₀).symm
      (baseChangePointsEquiv b G T g) = j.hom ≫ g := by
    apply (ChangeOfBase.pointsEquiv b G a₀).injective
    rw [MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    simp only [ChangeOfBase.pointsEquiv_left, Over.comp_left, baseChangePointsEquiv_left]
    change _ = (𝟙 T.left ≫ g.left) ≫ pullback.fst G.X.hom b
    rw [Category.id_comp]
  apply (baseChangePointsEquiv b H T).injective
  rw [baseChangeFamily_toFun, fromBaseChangeFamily_toFun]
  change ChangeOfBase.pointsEquiv b H a₀
    (e.toFun (ChangeOfBase.testPoint b a₀)
      ((ChangeOfBase.pointsEquiv b G a₀).symm (baseChangePointsEquiv b G T g))) = _
  rw [hg, ha, e.naturality]
  apply Over.OverMorphism.ext
  simp only [ChangeOfBase.pointsEquiv_left, Over.comp_left, baseChangePointsEquiv_left]
  change (𝟙 T.left ≫ (e.toFun a g).left) ≫ pullback.fst H.X.hom b = _
  rw [Category.id_comp]

/-- The full local isomorphism families are invariant under change of base of their tests. -/
def baseChangeEquiv : LocalGroupIso G H ((Over.map b).obj U) ≃
    LocalGroupIso ((baseChange b).obj G) ((baseChange b).obj H) U where
  toFun := baseChangeFamily b
  invFun := fromBaseChangeFamily b
  left_inv := fromBaseChangeFamily_baseChangeFamily b
  right_inv := baseChangeFamily_fromBaseChangeFamily b

/-- Transport commutes with every refinement of the new-base parameter scheme. -/
theorem baseChangeFamily_refine (e : LocalGroupIso G H ((Over.map b).obj U))
    {V : Over S'} (r : V ⟶ U) :
    (e.refine ((Over.map b).map r)).baseChangeFamily b = (e.baseChangeFamily b).refine r := by
  apply ext_toFun
  intro T a g
  apply (baseChangePointsEquiv b H T).injective
  rw [baseChangeFamily_toFun]
  change e.toFun (((Over.map b).map a) ≫ (Over.map b).map r)
    (baseChangePointsEquiv b G T g) =
    baseChangePointsEquiv b H T ((e.baseChangeFamily b).toFun (a ≫ r) g)
  rw [baseChangeFamily_toFun, Functor.map_comp]

end Langlands.GroupScheme.LocalGroupIso

namespace Langlands.GroupScheme.GroupIsomorphismScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}
    (I : GroupIsomorphismScheme G H)

/-- Pulling back the parameter scheme classifies the base-changed families on every test. -/
def baseChangePointsEquiv (T : Over S') :
    (T ⟶ (Over.pullback b).obj I.parameter) ≃
      LocalGroupIso ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H) T :=
  ((Over.mapPullbackAdj b).homEquiv T I.parameter).symm.trans
    ((I.pointsEquiv ((Over.map b).obj T)).trans (LocalGroupIso.baseChangeEquiv b))

/-- The universal local family on the actual pullback of a representing parameter scheme. -/
def baseChangeUniversalIso :
    LocalGroupIso ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H)
      ((Over.pullback b).obj I.parameter) :=
  (I.universalIso.refine ((Over.mapPullbackAdj b).counit.app I.parameter)).baseChangeFamily b

theorem baseChangeUniversalIso_refine {T : Over S'}
    (p : T ⟶ (Over.pullback b).obj I.parameter) :
    (I.baseChangeUniversalIso b).refine p = I.baseChangePointsEquiv b T p := by
  rw [baseChangeUniversalIso, ← LocalGroupIso.baseChangeFamily_refine]
  change (LocalGroupIso.baseChangeFamily b _ :
      LocalGroupIso ((GroupScheme.baseChange b).obj G)
        ((GroupScheme.baseChange b).obj H) T) = LocalGroupIso.baseChangeFamily b _
  congr 1

/-- Full group-isomorphism representability is preserved by arbitrary base change. -/
def baseChange :
    GroupIsomorphismScheme ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H) where
  parameter := (Over.pullback b).obj I.parameter
  universalIso := I.baseChangeUniversalIso b
  bijective T := by
    have h : (fun p : T ⟶ (Over.pullback b).obj I.parameter =>
        (I.baseChangeUniversalIso b).refine p) = I.baseChangePointsEquiv b T := by
      funext p
      exact I.baseChangeUniversalIso_refine b p
    rw [h]
    exact (I.baseChangePointsEquiv b T).bijective

@[simp] theorem baseChange_parameter :
    (I.baseChange b).parameter = (Over.pullback b).obj I.parameter := rfl

@[simp] theorem baseChange_universalIso :
    (I.baseChange b).universalIso =
      (I.universalIso.refine ((Over.mapPullbackAdj b).counit.app I.parameter)).baseChangeFamily b := rfl

end Langlands.GroupScheme.GroupIsomorphismScheme
