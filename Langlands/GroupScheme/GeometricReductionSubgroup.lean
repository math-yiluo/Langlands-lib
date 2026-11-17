import Langlands.GroupScheme.ReducedSubgroup
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # The reduced subgroup under geometric reducedness of the reduction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeometricReductionSubgroup

open ReducedSubgroup

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom]
  [GeometricallyReduced (redOver G).hom]

instance reduced_square : IsReduced (redOver G ⊗ redOver G).left := by
  have : IsLocallyNoetherian (redOver G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (redOver G).hom
  exact inferInstanceAs (IsReduced (pullback (redOver G).hom (redOver G).hom))

/-- The unit factors through the canonical reduction over any field. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ redOver G :=
  liftOver η[G.X]

omit [LocallyOfFiniteType G.X.hom] [GeometricallyReduced (redOver G).hom] in
@[reassoc (attr := simp)]
theorem one_fac : one G ≫ redOverι G = η[G.X] := liftOver_fac _

/-- Geometric reducedness makes the square reduced, so multiplication restricts. -/
def mul : redOver G ⊗ redOver G ⟶ redOver G :=
  liftOver ((redOverι G ⊗ₘ redOverι G) ≫ μ[G.X])

@[reassoc (attr := simp)]
theorem mul_fac : mul G ≫ redOverι G = (redOverι G ⊗ₘ redOverι G) ≫ μ[G.X] :=
  liftOver_fac _

/-- Inversion factors through the canonical reduction. -/
def inv : redOver G ⟶ redOver G := liftOver (redOverι G ≫ ι[G.X])

omit [LocallyOfFiniteType G.X.hom] [GeometricallyReduced (redOver G).hom] in
@[reassoc (attr := simp)]
theorem inv_fac : inv G ≫ redOverι G = redOverι G ≫ ι[G.X] := liftOver_fac _

instance groupObject : GrpObj (redOver G) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (redOverι G) (one G) (mul G) (inv G) (one_fac G) (mul_fac G) (inv_fac G)

instance inclusion_isMonHom : IsMonHom (redOverι G) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (redOverι G) (one G) (mul G) (inv G) (one_fac G) (mul_fac G) (inv_fac G)

/-- The actual reduced subgroup when its canonical reduction is geometrically reduced. -/
abbrev group : GroupScheme (Spec (CommRingCat.of k)) := { X := redOver G }

/-- The actual inclusion of the reduced subgroup. -/
def inclusion : group G ⟶ G := Grp.homMk (redOverι G)

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion G).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (redι G.X.left))

instance inclusion_surjective : Surjective (inclusion G).hom.hom.left :=
  ⟨redι_surjective G.X.left⟩

instance smooth : Smooth (group G).X.hom := by
  let : GrpObj (Over.mk (group G).X.hom) := groupObject G
  exact AlgebraicGeometry.smooth_of_grpObj (group G).X.hom

instance affine [IsAffineHom G.X.hom] : IsAffineHom (group G).X.hom :=
  inferInstanceAs (IsAffineHom (redι G.X.left ≫ G.X.hom))

end Langlands.GroupScheme.GeometricReductionSubgroup
