import Langlands.AlgebraicGeometry.Picard.RigidifiedClassMonoid
import Langlands.AlgebraicGeometry.Picard.TensorNaturality
import Langlands.AlgebraicGeometry.Picard.DualSchemeOrigin

/-! # The commutative-monoid presheaf of geometric Picard-zero classes -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- The actual tensor and trivial class on the geometric Picard-zero subset,
equipped with their proved commutative-monoid laws. -/
@[instance_reducible]
def picardZeroClassesCommMonoid (T : Over S) : CommMonoid (PicardZeroClasses A T) where
  mul := picardZeroClassesTensor preservation A T
  one := trivialPicardZeroClass A T
  mul_assoc := picardZeroClassesTensor_assoc preservation associativity comparison A T
  one_mul := picardZeroClassesTensor_left_unit preservation A unitCoherence T
  mul_one := picardZeroClassesTensor_right_unit preservation A unitCoherence T
  mul_comm := picardZeroClassesTensor_comm preservation symmetry A T

/-- Inclusion of geometric Picard-zero classes into rigidified classes preserves
the actual tensor and trivial class. -/
def picardZeroInclusionMonoidHom (T : Over S) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    letI := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
      comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) T
    PicardZeroClasses A T →* RigidifiedClasses A T := by
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  letI := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence associativity
    comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) T
  exact { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }

variable (composition : PullbackTensorCompositionStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})

/-- Actual parameter pullback as a monoid homomorphism on geometric Picard-zero classes. -/
def picardZeroClassesPullbackMonoidHom {T U : Over S} (h : T ⟶ U) :
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A U
    letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
      symmetry A T
    PicardZeroClasses A U →* PicardZeroClasses A T := by
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A U
  letI := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry A T
  exact
    { toFun := picardZeroClassesPullback stability A h
      map_one' := picardZeroClassesPullback_trivial stability A h
      map_mul' := picardZeroClassesPullback_tensor preservation composition unitCoherence.1
        stability A h }

/-- The geometric Picard-zero presheaf with values in commutative monoids. -/
def picardZeroMonoidPresheaf : (Over S)ᵒᵖ ⥤ CommMonCat.{u + 1} := by
  letI (T : Over S) := picardZeroClassesCommMonoid preservation unitCoherence associativity
    comparison symmetry A T
  exact
    { obj T := CommMonCat.of (PicardZeroClasses A T.unop)
      map h := CommMonCat.ofHom (picardZeroClassesPullbackMonoidHom preservation unitCoherence
        associativity comparison symmetry A composition stability h.unop)
      map_id T := by
        apply CommMonCat.ext
        intro q
        exact ConcreteCategory.congr_hom
          ((picardZeroPresheaf stability A RigidifiedModule.pullbackCoherence).map_id T) q
      map_comp h k := by
        apply CommMonCat.ext
        intro q
        exact ConcreteCategory.congr_hom
          ((picardZeroPresheaf stability A RigidifiedModule.pullbackCoherence).map_comp h k) q }

/-- Forgetting the monoids recovers the existing geometric Picard-zero presheaf. -/
def picardZeroMonoidPresheafForgetIso :
    picardZeroMonoidPresheaf preservation unitCoherence associativity comparison symmetry
        A composition stability ⋙ CategoryTheory.forget CommMonCat ≅
      picardZeroPresheaf stability A RigidifiedModule.pullbackCoherence :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro T U h; rfl)

/-- The geometric Picard-zero inclusion is a natural family of monoid homomorphisms. -/
def picardZeroMonoidInclusion :
    picardZeroMonoidPresheaf preservation unitCoherence associativity comparison symmetry
        A composition stability ⟶
      RigidifiedLineBundle.classMonoidPresheaf preservation unitCoherence associativity
        comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) composition := by
  letI (T : Over S) := picardZeroClassesCommMonoid preservation unitCoherence associativity
    comparison symmetry A T
  letI (T : Over S) := RigidifiedLineBundle.classesCommMonoid preservation unitCoherence
    associativity comparison symmetry A.X.hom (unitSection A) (unitSection_comp A) T
  exact
    { app T := CommMonCat.ofHom (picardZeroInclusionMonoidHom preservation unitCoherence
        associativity comparison symmetry A T.unop)
      naturality T U h := by ext q; rfl }

end Langlands.AbelianScheme
