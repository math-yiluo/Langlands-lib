import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorAssociativity
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorSymmetry
import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorPullback
import Langlands.AlgebraicGeometry.Picard.RigidifiedTrivialPullback
import Mathlib.Algebra.Category.MonCat.Basic

/-! # The commutative-monoid presheaf of rigidified line-bundle classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- The canonical trivial rigidified class over a test scheme. -/
def trivialClass (T : Over S) : Classes f ε section_eq T :=
  classOf f ε section_eq (trivial ((relativeSection f ε section_eq).app T))

/-- The existing tensor and trivial class, equipped with their proved monoid laws. -/
@[instance_reducible]
def classesCommMonoid (T : Over S) : CommMonoid (Classes f ε section_eq T) where
  mul := classesTensor preservation f ε section_eq T
  one := trivialClass f ε section_eq T
  mul_assoc := classesTensor_assoc preservation associativity comparison f ε section_eq T
  one_mul := classesTensor_left_unit preservation unitCoherence f ε section_eq T
  mul_one := classesTensor_right_unit preservation unitCoherence f ε section_eq T
  mul_comm := classesTensor_comm preservation symmetry f ε section_eq T

/-- Pullback preserves the canonical trivial rigidified class. -/
lemma classesPullback_trivialClass {T U : Over S} (h : T ⟶ U) :
    classesPullback f ε section_eq h (trivialClass f ε section_eq U) =
      trivialClass f ε section_eq T :=
  Quotient.sound ⟨pullbackTrivialIso ((relativeSpace f).map h) h.left
    ((relativeSection f ε section_eq).naturality h).symm⟩

variable (composition : PullbackTensorCompositionStatement.{u})

/-- Actual pullback on classes as a homomorphism of the constructed monoids. -/
def classesPullbackMonoidHom {T U : Over S} (h : T ⟶ U) :
    letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
      f ε section_eq U
    letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
      f ε section_eq T
    Classes f ε section_eq U →* Classes f ε section_eq T := by
  letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
    f ε section_eq U
  letI := classesCommMonoid preservation unitCoherence associativity comparison symmetry
    f ε section_eq T
  exact
    { toFun := classesPullback f ε section_eq h
      map_one' := classesPullback_trivialClass f ε section_eq h
      map_mul' := classesPullback_tensor preservation composition unitCoherence.1 f ε section_eq h }

/-- The rigidified class presheaf with values in commutative monoids. -/
def classMonoidPresheaf : (Over S)ᵒᵖ ⥤ CommMonCat.{u + 1} := by
  letI (T : Over S) := classesCommMonoid preservation unitCoherence associativity
    comparison symmetry f ε section_eq T
  exact
    { obj T := CommMonCat.of (Classes f ε section_eq T.unop)
      map h := CommMonCat.ofHom (classesPullbackMonoidHom preservation unitCoherence
        associativity comparison symmetry f ε section_eq composition h.unop)
      map_id T := by
        ext q
        exact ConcreteCategory.congr_hom
          ((classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq).map_id T) q
      map_comp h k := by
        ext q
        exact ConcreteCategory.congr_hom
          ((classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq).map_comp h k) q }

/-- Forgetting the monoid structure recovers the existing presheaf of classes. -/
def classMonoidPresheafForgetIso :
    classMonoidPresheaf preservation unitCoherence associativity comparison symmetry
        f ε section_eq composition ⋙ CategoryTheory.forget CommMonCat ≅
      classPresheaf RigidifiedModule.pullbackCoherence f ε section_eq :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro T U h; rfl)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
