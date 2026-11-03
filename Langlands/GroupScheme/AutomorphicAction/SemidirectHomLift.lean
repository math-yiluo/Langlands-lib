import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps

/-! # Lifting compatible homomorphisms from a semidirect group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {H N G : GroupScheme B}
variable (a : AutomorphicAction H N) (i : N ⟶ G) (j : H ⟶ G)
variable (hc : ∀ (T : Over B) (h : T ⟶ H.X) (n : T ⟶ N.X),
  a.act h n ≫ i.hom.hom =
    (h ≫ j.hom.hom) * (n ≫ i.hom.hom) * (h ≫ j.hom.hom)⁻¹)

/-- The natural point homomorphism obtained from compatible factor maps. -/
def semidirectHomLiftPoints : a.semidirectPoints ⟶ G.points where
  app T := GrpCat.ofHom (SemidirectProduct.lift
    ((pointsMap i).app T).hom ((pointsMap j).app T).hom (by
      intro h
      apply MonoidHom.ext
      intro n
      exact hc T.unop h n))
  naturality {T V} f := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change ((f.unop ≫ x.left) ≫ i.hom.hom) *
        ((f.unop ≫ x.right) ≫ j.hom.hom) =
      f.unop ≫ ((x.left ≫ i.hom.hom) * (x.right ≫ j.hom.hom))
    rw [MonObj.comp_mul, Category.assoc, Category.assoc]

/-- The actual homomorphism from the semidirect group scheme induced by
compatible maps from its normal and acting factors. -/
def semidirectHomLift : a.semidirectProduct ⟶ G :=
  yonedaGrpFullyFaithful.preimage
    (a.semidirectPointsIso.hom ≫ a.semidirectHomLiftPoints i j hc)

/-- On every relative test, the lifted homomorphism multiplies the images of
the two semidirect coordinates in their original order. -/
theorem semidirectHomLift_points {T : Over B} (x : T ⟶ a.semidirectProduct.X) :
    x ≫ (a.semidirectHomLift i j hc).hom.hom =
      ((a.semidirectPointsEquiv T x).left ≫ i.hom.hom) *
        ((a.semidirectPointsEquiv T x).right ≫ j.hom.hom) := by
  have hn : pointsMap (a.semidirectHomLift i j hc) =
      a.semidirectPointsIso.hom ≫ a.semidirectHomLiftPoints i j hc :=
    yonedaGrpFullyFaithful.map_preimage _
  exact congrArg (fun k => (k.app (op T)).hom x) hn

set_option backward.isDefEq.respectTransparency false in
/-- The underlying morphism of the lift is ordered multiplication of the two
universal factor images. -/
theorem semidirectHomLift_hom :
    (a.semidirectHomLift i j hc).hom.hom =
      (fst N.X H.X ≫ i.hom.hom) * (snd N.X H.X ≫ j.hom.hom) := by
  simpa only [semidirectPointsEquiv_left, semidirectPointsEquiv_right,
    Category.id_comp] using a.semidirectHomLift_points i j hc (𝟙 a.semidirectProduct.X)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem semidirectInl_comp_lift :
    a.semidirectInl ≫ a.semidirectHomLift i j hc = i := by
  apply Grp.hom_ext
  change a.semidirectInl.hom.hom ≫ (a.semidirectHomLift i j hc).hom.hom = i.hom.hom
  rw [semidirectHomLift_hom, semidirectInl_hom, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp, mul_one]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem semidirectInr_comp_lift :
    a.semidirectInr ≫ a.semidirectHomLift i j hc = j := by
  apply Grp.hom_ext
  change a.semidirectInr.hom.hom ≫ (a.semidirectHomLift i j hc).hom.hom = j.hom.hom
  rw [semidirectHomLift_hom, semidirectInr_hom, MonObj.comp_mul,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp, MonObj.one_comp, one_mul]

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.SubgroupFunctor

variable {B : Scheme.{u}} {G H N : GroupScheme B}
variable (i : H ⟶ G) (j : N ⟶ G)
variable (hn : (range i).IsNormalizedBy (range j)) [Mono i.hom.hom]

/-- Ordered multiplication as an actual homomorphism from the semidirect
product associated to normalized conjugation. -/
def normalizedProductHom :
    (AutomorphicAction.ofNormalizedConjugation i j hn).semidirectProduct ⟶ G :=
  (AutomorphicAction.ofNormalizedConjugation i j hn).semidirectHomLift i j
    (fun _T n h => lift_comp_normalizedConjugation_comp i j hn n h)

/-- The normalized semidirect multiplication homomorphism has the expected
underlying scheme map, with normal factor first. -/
theorem normalizedProductHom_hom :
    (normalizedProductHom i j hn).hom.hom =
      (fst H.X N.X ≫ i.hom.hom) * (snd H.X N.X ≫ j.hom.hom) :=
  AutomorphicAction.semidirectHomLift_hom _ _ _ _

end Langlands.GroupScheme.SubgroupFunctor
