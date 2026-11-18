import Langlands.GroupScheme.Cartier.Characters
import Langlands.AlgebraicGeometry.EtaleLocalSystem
import Langlands.GroupScheme.Torus.RelativeDiagonalizableHomLocality
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Evaluation of an abelian family of actual characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier

open Langlands.AlgebraicGeometry.EtaleLocalSystem

variable {S : Scheme.{u}} (G : CommGroupScheme S) (M : AddCommGrpCat.{u})

/-- A coefficient gives the corresponding constant section on each test scheme. -/
def constantCoefficient (T : Over S) : M →+ (constant S M).obj (op T) :=
  (constantSections S M T).symm.toAddMonoidHom.comp LocallyConstant.constAddMonoidHom

theorem constantCoefficient_restrict {T T' : Over S} (b : T' ⟶ T) (m : M) :
    (constant S M).map b.op (constantCoefficient M T m) = constantCoefficient M T' m := by
  apply (constantSections S M T').injective
  ext x
  rfl

variable (a : constant S M ⟶ characters G)

/-- The actual character labelled by `m`, on each test scheme. -/
def familyCharacter (T : Over S) : M →+ (characters G).obj (op T) :=
  (a.app (op T)).hom.comp (constantCoefficient M T)

theorem familyCharacter_restrict {T T' : Over S} (b : T' ⟶ T) (m : M) :
    (characters G).map b.op (familyCharacter G M a T m) =
      familyCharacter G M a T' m := by
  have h := ConcreteCategory.congr_hom (a.naturality b.op) (constantCoefficient M T m)
  change (a.app (op T')) ((constant S M).map b.op (constantCoefficient M T m)) =
    (characters G).map b.op (familyCharacter G M a T m) at h
  rw [constantCoefficient_restrict] at h
  exact h.symm

/-- Evaluate all characters in the family at a point, as an `M`-character in units. -/
def familyUnits (T : Over S) (x : T ⟶ G.X) :
    Multiplicative M →* Γ(T.left, ⊤)ˣ where
  toFun m := Gm.pointsEquiv S T (characterEvaluation (familyCharacter G M a T m.toAdd) x)
  map_one' := by
    change Gm.pointsEquiv S T (characterEvaluation (familyCharacter G M a T 0) x) = 1
    rw [map_zero, characterEvaluation_zero, map_one]
  map_mul' m n := by
    change Gm.pointsEquiv S T
        (characterEvaluation (familyCharacter G M a T (m.toAdd + n.toAdd)) x) = _
    rw [map_add, characterEvaluation_add, map_mul]

theorem familyUnits_restrict {T T' : Over S} (b : T' ⟶ T) (x : T ⟶ G.X) :
    familyUnits G M a T' (b ≫ x) =
      (Units.map b.left.appTop.hom.toMonoidHom).comp (familyUnits G M a T x) := by
  apply MonoidHom.ext
  intro m
  change Gm.pointsEquiv S T'
    (characterEvaluation (familyCharacter G M a T' m.toAdd) (b ≫ x)) =
      Units.map b.left.appTop.hom.toMonoidHom
        (Gm.pointsEquiv S T (characterEvaluation (familyCharacter G M a T m.toAdd) x))
  rw [← familyCharacter_restrict G M a b, characterEvaluation_restrict,
    Gm.pointsEquiv_naturality]

/-- Evaluating the family sends actual points of `G` to points of `D_S(M)`. -/
def familyPoints (T : Over S) :
    (T ⟶ G.X) →* (T ⟶ (RelativeMultiplicativeType.diagonalizable S M).X) where
  toFun x := (RelativeMultiplicativeType.pointsEquiv S M T).symm (familyUnits G M a T x)
  map_one' := by
    apply (RelativeMultiplicativeType.pointsEquiv S M T).injective
    rw [MulEquiv.apply_symm_apply, map_one]
    apply MonoidHom.ext
    intro m
    change Gm.pointsEquiv S T (characterEvaluation _ 1) = 1
    rw [characterEvaluation_one, map_one]
  map_mul' x y := by
    apply (RelativeMultiplicativeType.pointsEquiv S M T).injective
    rw [MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    apply MonoidHom.ext
    intro m
    change Gm.pointsEquiv S T (characterEvaluation _ (x * y)) = _
    rw [characterEvaluation_mul, map_mul]
    rfl

theorem familyPoints_naturality {T T' : Over S} (b : T' ⟶ T) (x : T ⟶ G.X) :
    familyPoints G M a T' (b ≫ x) = b ≫ familyPoints G M a T x := by
  apply (RelativeMultiplicativeType.pointsEquiv S M T').injective
  change RelativeMultiplicativeType.pointsEquiv S M T'
      ((RelativeMultiplicativeType.pointsEquiv S M T').symm (familyUnits G M a T' (b ≫ x))) =
    RelativeMultiplicativeType.pointsEquiv S M T'
      (b ≫ (RelativeMultiplicativeType.pointsEquiv S M T).symm (familyUnits G M a T x))
  rw [MulEquiv.apply_symm_apply, RelativeMultiplicativeType.pointsEquiv_comp,
    MulEquiv.apply_symm_apply, familyUnits_restrict]

/-- The actual group-scheme homomorphism obtained by evaluating the character family. -/
def characterFamilyHom : G.toGrp ⟶ RelativeMultiplicativeType.diagonalizable S M :=
  homOfPoints (familyPoints G M a) (familyPoints_naturality G M a)

/-- Each coordinate of the evaluation homomorphism is the specified actual character. -/
theorem characterFamilyHom_evaluation (T : Over S) (x : T ⟶ G.X) (m : M) :
    RelativeMultiplicativeType.pointsEquiv S M T
      (x ≫ (characterFamilyHom G M a).hom.hom) (.ofAdd m) =
        Gm.pointsEquiv S T (characterEvaluation (familyCharacter G M a T m) x) := by
  rw [characterFamilyHom, comp_homOfPoints]
  change (RelativeMultiplicativeType.pointsEquiv S M T
    ((RelativeMultiplicativeType.pointsEquiv S M T).symm (familyUnits G M a T x))) _ = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end Langlands.GroupScheme.Cartier
