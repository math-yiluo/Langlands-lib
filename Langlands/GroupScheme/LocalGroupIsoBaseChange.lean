import Langlands.GroupScheme.LocalGroupIso
import Langlands.AbelianScheme.KernelBaseChange

/-! # Base-change isomorphisms and natural local group isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- Regard a test scheme equipped with a point of `U` as a scheme over `U`. -/
def coverTest {T : Over S} (a : T ⟶ U) : Over U.left :=
  Over.mk a.left

/-- A map of tests also maps their induced tests over the cover. -/
def coverTestMap {T T' : Over S} (t : T' ⟶ T) (a : T ⟶ U) :
    coverTest (t ≫ a) ⟶ coverTest a :=
  Over.homMk t.left rfl

/-- Forgetting the cover point recovers the original test scheme. -/
def coverTestIso {T : Over S} (a : T ⟶ U) :
    (Over.map U.hom).obj (coverTest a) ≅ T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 T.left ≫ T.hom = a.left ≫ U.hom
    rw [Category.id_comp]
    exact (Over.w a).symm)

private def precompPointsEquiv {T T' : Over S} (i : T ≅ T')
    (G : GroupScheme S) : (T ⟶ G.X) ≃* (T' ⟶ G.X) where
  toFun g := i.inv ≫ g
  invFun g := i.hom ≫ g
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := MonObj.comp_mul _ _ _

/-- The pullback point equivalence at a specified point of the cover. -/
def coverPointsEquiv (G : GroupScheme S) {T : Over S} (a : T ⟶ U) :
    (coverTest a ⟶ ((baseChange U.hom).obj G).X) ≃* (T ⟶ G.X) :=
  (baseChangePointsEquiv U.hom G (coverTest a)).trans
    (precompPointsEquiv (coverTestIso a) G)

@[simp] theorem coverPointsEquiv_left (G : GroupScheme S) {T : Over S}
    (a : T ⟶ U) (x : coverTest a ⟶ ((baseChange U.hom).obj G).X) :
    (coverPointsEquiv G a x).left = x.left ≫ pullback.fst G.X.hom U.hom := by
  change (𝟙 T.left) ≫ (x.left ≫ pullback.fst G.X.hom U.hom) = _
  simp

/-- Projection of pullback points commutes with every map of relative tests. -/
theorem coverPointsEquiv_naturality (G : GroupScheme S)
    {T T' : Over S} (t : T' ⟶ T) (a : T ⟶ U)
    (x : coverTest a ⟶ ((baseChange U.hom).obj G).X) :
    coverPointsEquiv G (t ≫ a) (coverTestMap t a ≫ x) =
      t ≫ coverPointsEquiv G a x := by
  apply Over.OverMorphism.ext
  simp [Category.assoc, coverTestMap]

theorem coverPointsEquiv_symm_naturality (G : GroupScheme S)
    {T T' : Over S} (t : T' ⟶ T) (a : T ⟶ U) (g : T ⟶ G.X) :
    (coverPointsEquiv G (t ≫ a)).symm (t ≫ g) =
      coverTestMap t a ≫ (coverPointsEquiv G a).symm g := by
  apply (coverPointsEquiv G (t ≫ a)).injective
  rw [MulEquiv.apply_symm_apply, coverPointsEquiv_naturality,
    MulEquiv.apply_symm_apply]

private def isoPointsEquiv {V : Scheme.{u}} {J K : GroupScheme V}
    (e : J ≅ K) (T : Over V) : (T ⟶ J.X) ≃* (T ⟶ K.X) where
  toFun g := g ≫ e.hom.hom.hom
  invFun g := g ≫ e.inv.hom.hom
  left_inv g := by
    change g ≫ (e.hom ≫ e.inv).hom.hom = g
    rw [e.hom_inv_id]
    exact Category.comp_id g
  right_inv g := by
    change g ≫ (e.inv ≫ e.hom).hom.hom = g
    rw [e.inv_hom_id]
    exact Category.comp_id g
  map_mul' g h := MonObj.mul_comp _ _ _

/-- An actual isomorphism after base change gives local isomorphisms on all tests. -/
def ofBaseChangeIso
    (e : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H) :
    LocalGroupIso G H U where
  toFun a := (coverPointsEquiv G a).symm.trans
    ((isoPointsEquiv e (coverTest a)).trans (coverPointsEquiv H a))
  naturality t a g := by
    change coverPointsEquiv H (t ≫ a)
        ((coverPointsEquiv G (t ≫ a)).symm (t ≫ g) ≫ e.hom.hom.hom) =
      t ≫ coverPointsEquiv H a
        ((coverPointsEquiv G a).symm g ≫ e.hom.hom.hom)
    rw [coverPointsEquiv_symm_naturality, Category.assoc,
      coverPointsEquiv_naturality]

/-- The local map is evaluated by lifting to the pullback and projecting the image. -/
theorem ofBaseChangeIso_toFun_left
    (e : (baseChange U.hom).obj G ≅ (baseChange U.hom).obj H)
    {T : Over S} (a : T ⟶ U) (g : T ⟶ G.X) :
    ((ofBaseChangeIso e).toFun a g).left =
      ((coverPointsEquiv G a).symm g).left ≫
        e.hom.hom.hom.left ≫ pullback.fst H.X.hom U.hom := by
  change (coverPointsEquiv H a
    ((coverPointsEquiv G a).symm g ≫ e.hom.hom.hom)).left = _
  rw [coverPointsEquiv_left]
  exact Category.assoc _ _ _

end Langlands.GroupScheme.LocalGroupIso
