import Langlands.AlgebraicGeometry.Picard.RigidifiedClassGroup
import Langlands.AlgebraicGeometry.Picard.UniversalFamilyTriviality
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # The commutative group object on a universal rigidified parameter

A universal rigidified line bundle on `X ×_S P` makes `Hom_S(-, P)` the presheaf of
rigidified line-bundle classes. That presheaf is a presheaf of commutative groups under the
tensor product, so `P` is a commutative group object of `Over S`.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (localComparison : ∀ Y : Scheme.{u}, LocallyFreeRankOneIffTensorInvertibleStatement Y)
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)
variable (composition : PullbackTensorCompositionStatement.{u})

/-- The presheaf of rigidified line-bundle classes with the tensor product written
multiplicatively. -/
def classCommGrpPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1} :=
  classGroupPresheaf preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition ⋙ AddCommGrpCat.toCommGrp

variable {P : Over S} (L : relative f ε section_eq P) (hL : IsUniversal f ε section_eq L)

/-- A universal rigidified bundle on `P` represents the underlying presheaf of sets of the
multiplicative class presheaf; the bijection is the classifying map. -/
def universalClassRepresentableBy :
    (classCommGrpPresheaf preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition ⋙ CategoryTheory.forget CommGrpCat).RepresentableBy
        P where
  homEquiv := classifyingEquiv f ε section_eq L hL _
  homEquiv_comp h k := classifyingMap_comp f ε section_eq RigidifiedModule.pullbackCoherence L h k

/-- The commutative group object structure on a universal rigidified parameter, transported from
the tensor group of rigidified classes through the representation. -/
@[instance_reducible]
def universalCommGrpObj : CommGrpObj P :=
  CommGrpObj.ofRepresentableBy P _
    (universalClassRepresentableBy preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL)

/-- For every test object `T`, the classifying map is a group isomorphism from `T`-points of the
universal parameter to rigidified classes on `X ×_S T`. -/
def universalPointMulEquiv (T : Over S) :
    letI := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL
    letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq T
    (T ⟶ P) ≃* Classes f ε section_eq T := by
  let := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq composition L hL
  let := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  let α := universalClassRepresentableBy preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq composition L hL
  exact
    { toEquiv := classifyingEquiv f ε section_eq L hL T
      map_mul' p q := by
        change α.homEquiv' (CartesianMonoidalCategory.lift p q ≫ α.homEquiv'.symm
          (α.homEquiv' (CartesianMonoidalCategory.fst P P) *
            α.homEquiv' (CartesianMonoidalCategory.snd P P))) = α.homEquiv' p * α.homEquiv' q
        simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
        simp only [← α.homEquiv'_comp]
        simp }

/-- The underlying function of `universalPointMulEquiv` is the classifying map. -/
lemma universalPointMulEquiv_apply (T : Over S) (p : T ⟶ P) :
    universalPointMulEquiv preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL T p = classifyingMap f ε section_eq L T p :=
  rfl

/-- The classifying map sends the product of points to the tensor product of classes. -/
lemma classifyingMap_mul (T : Over S) (p q : T ⟶ P) :
    letI := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL
    letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq T
    classifyingMap f ε section_eq L T (p * q) =
      classifyingMap f ε section_eq L T p * classifyingMap f ε section_eq L T q := by
  let := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq composition L hL
  let := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  exact map_mul (universalPointMulEquiv preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq composition L hL T) p q

/-- The classifying map sends the inverse of a point to the inverse class. -/
lemma classifyingMap_inv (T : Over S) (p : T ⟶ P) :
    letI := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL
    letI := classesCommGroup preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq T
    classifyingMap f ε section_eq L T p⁻¹ = (classifyingMap f ε section_eq L T p)⁻¹ := by
  let := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq composition L hL
  let := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  exact map_inv (universalPointMulEquiv preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq composition L hL T) p

/-- The classifying map sends the identity point to the trivial rigidified class. -/
lemma classifyingMap_one (T : Over S) :
    letI := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL
    classifyingMap f ε section_eq L T 1 = trivialClass f ε section_eq T := by
  let := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq composition L hL
  let := classesCommGroup preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq T
  exact map_one (universalPointMulEquiv preservation unitCoherence associativity comparison
    symmetry localComparison f ε section_eq composition L hL T)

/-- The identity section of the group object is the published trivial parameter. -/
lemma one_eq_trivialParameter :
    letI := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
      localComparison f ε section_eq composition L hL
    (1 : Over.mk (𝟙 S) ⟶ P) = trivialParameter f ε section_eq L hL := by
  let := universalCommGrpObj preservation unitCoherence associativity comparison symmetry
    localComparison f ε section_eq composition L hL
  apply (hL _).injective
  rw [classifyingMap_one, trivialParameter, classifyFamily_spec]
  rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
