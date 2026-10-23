import Langlands.AlgebraicGeometry.Picard.RigidifiedTensorPullback
import Langlands.AlgebraicGeometry.Picard.RelativePicardZeroTensor
import Langlands.AlgebraicGeometry.Picard.PicardZeroSubfunctor
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Functor.Currying

/-! # Tensor as a natural operation on rigidified Picard presheaves -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
variable (pullbackCoherence : RigidifiedModule.PullbackCoherenceStatement.{u})
variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S)

/-- Tensor is a natural binary operation on the rigidified class presheaf. -/
def classTensorNatTrans :
    (classPresheaf pullbackCoherence f ε section_eq).prod'
        (classPresheaf pullbackCoherence f ε section_eq) ⋙
      Functor.uncurry.obj Limits.Types.binaryProductFunctor ⟶
        classPresheaf pullbackCoherence f ε section_eq where
  app T := TypeCat.ofHom (fun qr ↦ classesTensor preservation f ε section_eq T.unop qr.1 qr.2)
  naturality T U h := by
    ext qr
    exact (classesPullback_tensor preservation composition unitCoherence
      f ε section_eq h.unop qr.1 qr.2).symm

/-- The component of natural tensor is the actual class tensor operation. -/
@[simp] lemma classTensorNatTrans_app (T : Over S) (q r : Classes f ε section_eq T) :
    (classTensorNatTrans preservation composition unitCoherence pullbackCoherence
      f ε section_eq).app (op T) (q, r) = classesTensor preservation f ε section_eq T q r := rfl

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorLeftUnitorStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include composition unitCoherence in
/-- Pullback preserves the tensor product on the geometric Picard-zero subset. -/
lemma picardZeroClassesPullback_tensor {T U : Over S} (h : T ⟶ U)
    (q r : PicardZeroClasses A U) :
    picardZeroClassesPullback stability A h (picardZeroClassesTensor preservation A U q r) =
      picardZeroClassesTensor preservation A T
        (picardZeroClassesPullback stability A h q) (picardZeroClassesPullback stability A h r) := by
  apply Subtype.ext
  exact RigidifiedLineBundle.classesPullback_tensor preservation composition unitCoherence
    A.X.hom (unitSection A) (unitSection_comp A) h q.val r.val

variable (pullbackCoherence : RigidifiedModule.PullbackCoherenceStatement.{u})

/-- Tensor is a natural binary operation on the geometric Picard-zero presheaf. -/
def picardZeroTensorNatTrans :
    (picardZeroPresheaf stability A pullbackCoherence).prod'
        (picardZeroPresheaf stability A pullbackCoherence) ⋙
      Functor.uncurry.obj Limits.Types.binaryProductFunctor ⟶
        picardZeroPresheaf stability A pullbackCoherence where
  app T := TypeCat.ofHom (fun qr ↦ picardZeroClassesTensor preservation A T.unop qr.1 qr.2)
  naturality T U h := by
    ext qr
    exact (picardZeroClassesPullback_tensor preservation composition unitCoherence
      stability A h.unop qr.1 qr.2).symm

/-- The component of natural Picard-zero tensor is the existing restricted tensor. -/
@[simp] lemma picardZeroTensorNatTrans_app (T : Over S) (q r : PicardZeroClasses A T) :
    (picardZeroTensorNatTrans preservation composition unitCoherence stability A
      pullbackCoherence).app (op T) (q, r) = picardZeroClassesTensor preservation A T q r := rfl

/-- The inclusion of Picard-zero classes preserves the natural tensor operation. -/
lemma picardZeroTensorNatTrans_inclusion (T : Over S) (q r : PicardZeroClasses A T) :
    (picardZeroInclusion stability A pullbackCoherence).app (op T)
        ((picardZeroTensorNatTrans preservation composition unitCoherence stability A
          pullbackCoherence).app (op T) (q, r)) =
      (RigidifiedLineBundle.classTensorNatTrans preservation composition unitCoherence
        pullbackCoherence A.X.hom (unitSection A) (unitSection_comp A)).app (op T)
          ((picardZeroInclusion stability A pullbackCoherence).app (op T) q,
            (picardZeroInclusion stability A pullbackCoherence).app (op T) r) := rfl

end Langlands.AbelianScheme
