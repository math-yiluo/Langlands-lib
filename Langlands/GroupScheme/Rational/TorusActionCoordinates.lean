import Langlands.GroupScheme.Rational.TorusWeightSubgroups
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Lie.AffineCoordinates

/-! # Actual split-torus actions in corepresented coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace AutomorphicAction

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    {I : Type u} [Finite I]
    (b : AutomorphicAction H G) (e : H ≅ splitTorus (Spec R) I)

/-- The actual acting point corresponding to a family of units in a splitting. -/
def torusPoint {A : CommAlgCat.{u} R} (t : I → Aˣ) : H.affinePoints A :=
  (splitTorus.algebraPointsEquiv I A).symm t ≫ e.inv.hom.hom

@[simp] theorem torusPoint_one {A : CommAlgCat.{u} R} :
    torusPoint e (1 : I → Aˣ) = 1 := by
  simp [torusPoint]

theorem torusPoint_mul {A : CommAlgCat.{u} R} (t t' : I → Aˣ) :
    torusPoint e (t * t') = torusPoint e t * torusPoint e t' := by
  simp [torusPoint, MonObj.mul_comp]

theorem torusPoint_naturality {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (t : I → Aˣ) :
    H.affinePointMap f (torusPoint e t) =
      torusPoint e (fun i => Units.map f.hom.toMonoidHom (t i)) := by
  have h :
      Lie.affineMap (splitTorus (Spec R) I) f.hom
          ((splitTorus.algebraPointsEquiv I A).symm t) =
        (splitTorus.algebraPointsEquiv I A').symm
          (fun i => Units.map f.hom.toMonoidHom (t i)) := by
    apply (splitTorus.algebraPointsEquiv I A').injective
    rw [splitTorus.algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
  simpa only [torusPoint, affinePointMap_apply, Lie.affineMap_apply,
    CommAlgCat.ofHom_hom, Category.assoc]
    using congrArg (· ≫ e.inv.hom.hom) h

/-- An actual automorphic action, expressed in the unit coordinates of a split torus.
The target functor is the original group's actual affine points. -/
def toCorepresentedTorusAction : Corepresented.TorusAction G.affinePointFunctor I where
  act t x := b.act (torusPoint e t) x
  act_one x := by rw [torusPoint_one, b.act_one_left]
  act_mul t t' x := by rw [torusPoint_mul, b.act_mul_left]
  act_map_mul t x y := b.act_mul_right _ x y
  naturality f t x := by
    change G.affinePointMap f (b.act (torusPoint e t) x) =
      b.act (torusPoint e (fun i => Units.map f.hom.toMonoidHom (t i)))
        (G.affinePointMap f x)
    rw [affinePointMap_apply, b.naturality]
    change b.act (H.affinePointMap f (torusPoint e t)) (G.affinePointMap f x) = _
    rw [torusPoint_naturality]

@[simp] theorem toCorepresentedTorusAction_act {A : CommAlgCat.{u} R}
    (t : I → Aˣ) (x : G.affinePoints A) :
    (b.toCorepresentedTorusAction e).act t x = b.act (torusPoint e t) x := rfl

/-- Returning from unit coordinates recovers every original acting point. -/
theorem toCorepresentedTorusAction_act_point {A : CommAlgCat.{u} R}
    (h : H.affinePoints A) (x : G.affinePoints A) :
    (b.toCorepresentedTorusAction e).act
        (splitTorus.algebraPointsEquiv I A (h ≫ e.hom.hom.hom)) x = b.act h x := by
  simp only [toCorepresentedTorusAction_act, torusPoint, MulEquiv.symm_apply_apply,
    Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]

end AutomorphicAction

namespace TorusActionCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- The existing affine coordinate algebra corepresents the original group point functor. -/
abbrev corepresentation :
    (G.affinePointFunctor ⋙ forget GrpCat).CorepresentableBy (Lie.coordinateAlgebra G) :=
  AffineLinearEmbedding.corepresentableBy G (Lie.coordinateIso G)

@[simp] theorem coord_eq_pointCoordinates {A : CommAlgCat.{u} R} (x : G.affinePoints A) :
    Corepresented.coord (corepresentation G) x = Lie.pointCoordinates G x := rfl

/-- The coordinate construction recovers the actual group as a group scheme. -/
abbrev groupSchemeIso :
    Corepresented.groupScheme G.affinePointFunctor (corepresentation G) ≅ G :=
  AffineLinearEmbedding.modelIso G (Lie.coordinateIso G)

end TorusActionCoordinates

end Langlands.GroupScheme
