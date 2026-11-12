import Langlands.GroupScheme.Quaternionic.NormSquareCover
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.AbelianScheme.Multiplication

/-! # The actual group scheme of norm-square pairs -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

local notation "B" => Spec (CommRingCat.of K)

/-- The actual pullback of the reduced-norm character along the square map. -/
def normSquare : GroupScheme B :=
  pullback (reducedNormHom K A) (multiplication ((Gm B).toGrp) 2)

/-- The algebra-unit coordinate of the actual norm-square group scheme. -/
def normSquareπ : normSquare K A ⟶ groupScheme K A :=
  pullback.fst (reducedNormHom K A) (multiplication ((Gm B).toGrp) 2)

/-- The scalar square-root coordinate. -/
def normSquareRootHom : normSquare K A ⟶ ((Gm B).toGrp) :=
  pullback.snd (reducedNormHom K A) (multiplication ((Gm B).toGrp) 2)

/-- The actual defining equation of the pullback. -/
theorem normSquare_condition :
    normSquareπ K A ≫ reducedNormHom K A =
      normSquareRootHom K A ≫ multiplication ((Gm B).toGrp) 2 := pullback.condition

/-- The underlying relative schemes form the same pullback square. -/
theorem normSquare_isPullback :
    IsPullback (normSquareπ K A).hom.hom (normSquareRootHom K A).hom.hom
      (reducedNormHom K A).hom.hom (multiplication ((Gm B).toGrp) 2).hom.hom :=
  IsPullback.map (Grp.forget (Over B))
    (IsPullback.of_hasPullback (reducedNormHom K A) (multiplication ((Gm B).toGrp) 2))

/-- The actual coefficient algebra of a relative test scheme. -/
abbrev normSquareCoefficients (T : Over B) :=
  ((algΓ (CommRingCat.of K)).obj T).unop

private theorem normSquare_point_condition (T : Over B) (x : T ⟶ (normSquare K A).X) :
    Langlands.CentralSimple.reducedNormUnits K A (normSquareCoefficients K T)
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T
        (x ≫ (normSquareπ K A).hom.hom)) =
      Gm.pointsEquiv B T (x ≫ (normSquareRootHom K A).hom.hom) ^ 2 := by
  rw [← reducedNormHom_points]
  have h :
      (x ≫ (normSquareπ K A).hom.hom) ≫ (reducedNormHom K A).hom.hom =
        (x ≫ (normSquareRootHom K A).hom.hom) ≫ (multiplication ((Gm B).toGrp) 2).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f : normSquare K A ⟶ ((Gm B).toGrp) => x ≫ f.hom.hom)
        (normSquare_condition K A)
  rw [h, points_multiplication, map_zpow]
  rfl

/-- Map actual relative points to their two unit coordinates. -/
def normSquarePointHom (T : Over B) :
    (T ⟶ (normSquare K A).X) →*
      Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T) where
  toFun x := ⟨
    (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T
      (x ≫ (normSquareπ K A).hom.hom),
    Gm.pointsEquiv B T (x ≫ (normSquareRootHom K A).hom.hom)),
    normSquare_point_condition K A T x⟩
  map_one' := by
    apply Subtype.ext
    simp only [MonObj.one_comp, map_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    simp only [MonObj.mul_comp, map_mul]
    rfl

private theorem normSquare_lift_condition (T : Over B)
    (x : Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T)) :
    (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T).symm x.val.1 ≫
        (reducedNormHom K A).hom.hom =
      (Gm.pointsEquiv B T).symm x.val.2 ≫ (multiplication ((Gm B).toGrp) 2).hom.hom := by
  apply (Gm.pointsEquiv B T).injective
  rw [reducedNormHom_points, points_multiplication, map_zpow,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact x.property

/-- Construct the unique relative point from a norm-square pair of actual units. -/
def normSquarePoint (T : Over B)
    (x : Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T)) :
    T ⟶ (normSquare K A).X :=
  (normSquare_isPullback K A).lift
    ((FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T).symm x.val.1)
    ((Gm.pointsEquiv B T).symm x.val.2) (normSquare_lift_condition K A T x)

@[reassoc (attr := simp)]
theorem normSquarePoint_π (T : Over B)
    (x : Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T)) :
    normSquarePoint K A T x ≫ (normSquareπ K A).hom.hom =
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T).symm x.val.1 :=
  (normSquare_isPullback K A).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem normSquarePoint_root (T : Over B)
    (x : Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T)) :
    normSquarePoint K A T x ≫ (normSquareRootHom K A).hom.hom =
      (Gm.pointsEquiv B T).symm x.val.2 :=
  (normSquare_isPullback K A).lift_snd _ _ _

/-- Actual points of the pullback are exactly the norm-square pairs on every test scheme. -/
def normSquarePointsEquiv (T : Over B) :
    (T ⟶ (normSquare K A).X) ≃*
      Langlands.CentralSimple.normSquareCover K A (normSquareCoefficients K T) where
  toFun := normSquarePointHom K A T
  invFun := normSquarePoint K A T
  left_inv x := by
    apply (normSquare_isPullback K A).hom_ext
    · rw [normSquarePoint_π]
      exact (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T).symm_apply_apply _
    · rw [normSquarePoint_root]
      exact (Gm.pointsEquiv B T).symm_apply_apply _
  right_inv x := by
    apply Subtype.ext
    change
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T
        (normSquarePoint K A T x ≫ (normSquareπ K A).hom.hom),
      Gm.pointsEquiv B T
        (normSquarePoint K A T x ≫ (normSquareRootHom K A).hom.hom)) = x.val
    rw [normSquarePoint_π, normSquarePoint_root,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact Prod.mk.eta
  map_mul' := (normSquarePointHom K A T).map_mul

/-- The point comparison respects the actual projection to algebra units. -/
@[simp] theorem normSquarePointsEquiv_projection (T : Over B)
    (x : T ⟶ (normSquare K A).X) :
    Langlands.CentralSimple.normSquareProjection K A (normSquareCoefficients K T)
      (normSquarePointsEquiv K A T x) =
      FiniteAlgebraUnits.pointsEquiv (Module.finBasis K A) T
        (x ≫ (normSquareπ K A).hom.hom) := rfl

/-- The point comparison respects the actual square-root character. -/
@[simp] theorem normSquarePointsEquiv_root (T : Over B)
    (x : T ⟶ (normSquare K A).X) :
    Langlands.CentralSimple.normSquareRoot K A (normSquareCoefficients K T)
      (normSquarePointsEquiv K A T x) =
      Gm.pointsEquiv B T (x ≫ (normSquareRootHom K A).hom.hom) := rfl

end Langlands.GroupScheme.CentralSimpleUnits
