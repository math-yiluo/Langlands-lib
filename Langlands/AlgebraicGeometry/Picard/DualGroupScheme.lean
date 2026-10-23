import Langlands.AlgebraicGeometry.Picard.DualSchemeInverse
import Langlands.AbelianScheme.GroupScheme

/-! # The commutative group scheme of a chosen dual -/

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)
variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (M : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluation : tensorObj (poincareFamily A hA).obj.carrier M.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (stability : PicardZeroPullbackStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})

/-- The actual dual-point groups form a presheaf under parameter precomposition. -/
def dualPointGroupPresheafFromEvaluation : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} := by
  letI (T : Over S) := dualPointCommGroupFromEvaluation A hA preservation M evaluation
    stability composition unitCoherence associativity comparison symmetry T
  exact
    { obj := fun T ↦ CommGrpCat.of (unop T ⟶ dualScheme A hA)
      map := fun h ↦ CommGrpCat.ofHom
        (dualPointPullbackMonoidHom stability A hA preservation composition unitCoherence
          associativity comparison symmetry h.unop)
      map_id := fun T ↦ by
        apply CommGrpCat.ext
        intro p
        exact Category.id_comp p
      map_comp := fun f g ↦ by
        apply CommGrpCat.ext
        intro p
        exact Category.assoc g.unop f.unop p }

/-- The representing map of the point presheaf is the identity on scheme morphisms. -/
def dualPointGroupRepresentableBy :
    (dualPointGroupPresheafFromEvaluation A hA preservation M evaluation stability composition
      unitCoherence associativity comparison symmetry ⋙
        CategoryTheory.forget CommGrpCat).RepresentableBy (dualScheme A hA) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- The chosen dual is a commutative group scheme with the constructed point operations. -/
def dualCommGroupSchemeFromEvaluation : CommGroupScheme S := by
  letI := CommGrpObj.ofRepresentableBy (dualScheme A hA)
    (dualPointGroupPresheafFromEvaluation A hA preservation M evaluation stability composition
      unitCoherence associativity comparison symmetry)
    (dualPointGroupRepresentableBy A hA preservation M evaluation stability composition
      unitCoherence associativity comparison symmetry)
  exact { Grp.mk (dualScheme A hA) with comm := inferInstance }

local notation "D" => dualScheme A hA
local notation "G" => dualCommGroupSchemeFromEvaluation A hA preservation M evaluation
  stability composition unitCoherence associativity comparison symmetry
local notation "F" => dualPointGroupPresheafFromEvaluation A hA preservation M evaluation
  stability composition unitCoherence associativity comparison symmetry
local notation "α" => dualPointGroupRepresentableBy A hA preservation M evaluation
  stability composition unitCoherence associativity comparison symmetry

@[simp] lemma dualCommGroupSchemeFromEvaluation_X : (G).X = D := rfl

/-- The reconstructed multiplication is tensor classification after the canonical product map. -/
lemma dualCommGroupSchemeFromEvaluation_mul :
    μ[(G).X] =
      prod.lift (CartesianMonoidalCategory.fst D D) (CartesianMonoidalCategory.snd D D) ≫
        dualTensor stability A hA preservation := rfl

/-- On the categorical product used for `dualTensor`, the two multiplications agree. -/
lemma dualCommGroupSchemeFromEvaluation_prod_mul :
    CartesianMonoidalCategory.lift (prod.fst : D ⨯ D ⟶ D) prod.snd ≫ μ[(G).X] =
      dualTensor stability A hA preservation := by
  change CartesianMonoidalCategory.lift (prod.fst : D ⨯ D ⟶ D) prod.snd ≫
    (prod.lift (CartesianMonoidalCategory.fst D D) (CartesianMonoidalCategory.snd D D) ≫
      dualTensor stability A hA preservation) = _
  simp only [← Category.assoc, prod.comp_lift, CartesianMonoidalCategory.lift_fst,
    CartesianMonoidalCategory.lift_snd, prod.lift_fst_snd, Category.id_comp]

/-- The reconstructed inverse is the actual inverse-classifying morphism. -/
lemma dualCommGroupSchemeFromEvaluation_inv :
    ι[(G).X] = dualInverseFromEvaluation A hA preservation M evaluation := by
  change 𝟙 D ≫ dualInverseFromEvaluation A hA preservation M evaluation = _
  exact Category.id_comp _

/-- The reconstructed unit is the origin, after the structural map of the chosen terminal. -/
lemma dualCommGroupSchemeFromEvaluation_one :
    η[(G).X] =
      (Over.homMk (MonoidalCategory.tensorUnit (Over S)).hom :
        MonoidalCategory.tensorUnit (Over S) ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA := rfl

/-- The actual group scheme recovers the point presheaf, with identity components. -/
def dualCommGroupSchemePointsIso :
    Langlands.GroupScheme.points (G).toGrp ≅ F ⋙ CategoryTheory.forget₂ CommGrpCat GrpCat :=
  yonedaGrpObjIsoOfRepresentableBy D (F ⋙ CategoryTheory.forget₂ CommGrpCat GrpCat) α

@[simp] lemma dualCommGroupSchemePointsIso_apply (T : Over S) (p : T ⟶ (G).X) :
    (dualCommGroupSchemePointsIso A hA preservation M evaluation stability composition
      unitCoherence associativity comparison symmetry).hom.app (op T) p = p := rfl

/-- Poincare pullback classifies the points of the actual group scheme multiplicatively. -/
def dualCommGroupSchemePointMulEquiv (T : Over S) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    (T ⟶ (G).X) ≃* PicardZeroClasses A T := by
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  exact ((dualCommGroupSchemePointsIso A hA preservation M evaluation stability composition
    unitCoherence associativity comparison symmetry).app (op T)).groupIsoToMulEquiv.trans
      (dualPointMulEquiv stability A hA preservation composition unitCoherence associativity
        comparison symmetry T)

@[simp] lemma dualCommGroupSchemePointMulEquiv_apply (T : Over S) (p : T ⟶ (G).X) :
    dualCommGroupSchemePointMulEquiv A hA preservation M evaluation stability composition
      unitCoherence associativity comparison symmetry T p = dualPointClass stability A hA p := rfl

end Langlands.AbelianScheme
