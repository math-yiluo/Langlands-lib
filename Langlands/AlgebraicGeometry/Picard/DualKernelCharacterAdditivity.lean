import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AbelianScheme.KernelCharacterTensor

/-! # Additivity of the actual dual-kernel character -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (stability : PicardZeroPullbackStatement.{u})
  (f : A ⟶ B) (hB : HasDualScheme B)
  (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

/-- The tensor of the actual representatives computes tensor of the point classes. -/
lemma dualPointFamily_tensor_class {T : Over S} (p q : T ⟶ dualScheme B hB) :
    RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B)
        (RigidifiedLineBundle.tensor preservation
          (dualPointFamily B hB p) (dualPointFamily B hB q)) =
      (picardZeroClassesTensor preservation B T
        (dualPointClass stability B hB p) (dualPointClass stability B hB q)).val := by
  rw [picardZeroClassesTensor_val,
    ← dualPointFamily_class B hB stability p, ← dualPointFamily_class B hB stability q,
    RigidifiedLineBundle.classesTensor_classOf]

/-- Forgetting rigidification preserves the tensor pullback triviality. -/
lemma hasTrivialHomPullback_rigidified_tensor {T : Over S}
    (L K : RigidifiedFamily B T)
    (hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L))
    (hK : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj K)) :
    HasTrivialHomPullback f T
      ((RigidifiedLineBundle.forget _).obj (RigidifiedLineBundle.tensor preservation L K)) :=
  hasTrivialHomPullback_tensor preservation f
    ((RigidifiedLineBundle.forget _).obj L) ((RigidifiedLineBundle.forget _).obj K) hL hK

/-- The character tensor law also applies to the underlying rigidified families. -/
lemma trivialHomPullbackCharacter_rigidified_tensor {T : Over S}
    (L K : RigidifiedFamily B T)
    (hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L))
    (hK : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj K)) :
    trivialHomPullbackCharacter f (universalGlobalFunctions A)
        ((RigidifiedLineBundle.forget _).obj (RigidifiedLineBundle.tensor preservation L K))
        (hasTrivialHomPullback_rigidified_tensor f preservation L K hL hK) =
      trivialHomPullbackCharacter f (universalGlobalFunctions A)
          ((RigidifiedLineBundle.forget _).obj L) hL +
        trivialHomPullbackCharacter f (universalGlobalFunctions A)
          ((RigidifiedLineBundle.forget _).obj K) hK :=
  trivialHomPullbackCharacter_tensor preservation f (universalGlobalFunctions A)
    ((RigidifiedLineBundle.forget _).obj L) ((RigidifiedLineBundle.forget _).obj K) hL hK

/-- Tensor classification of ordinary dual points gives addition of their characters. -/
lemma dualKernelCharacter_tensor_of_class {T : Over S}
    (p q r : T ⟶ dualScheme B hB)
    (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (hq : q ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (hr : r ≫ dualSchemeMap homPicardZeroPullback f hA hB =
      (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)
    (hc : dualPointClass stability B hB r =
      picardZeroClassesTensor preservation B T
        (dualPointClass stability B hB p) (dualPointClass stability B hB q)) :
    dualKernelCharacter hA stability f hB r hr =
      dualKernelCharacter hA stability f hB p hp +
        dualKernelCharacter hA stability f hB q hq := by
  let L := dualPointFamily B hB p
  let K := dualPointFamily B hB q
  have hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L) :=
    ⟨dualKernelPullbackModuleIso hA stability f hB p hp⟩
  have hK : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj K) :=
    ⟨dualKernelPullbackModuleIso hA stability f hB q hq⟩
  have ht :
      HasTrivialHomPullback f T
        ((RigidifiedLineBundle.forget _).obj (RigidifiedLineBundle.tensor preservation L K)) :=
    hasTrivialHomPullback_rigidified_tensor f preservation L K hL hK
  have he :
      RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B)
          (RigidifiedLineBundle.tensor preservation L K) =
        (dualPointClass stability B hB r).val := by
    exact (dualPointFamily_tensor_class stability hB preservation p q).trans
      (congrArg Subtype.val hc).symm
  have hpe := dualKernelCharacter_eq_of_family_class hA stability f hB p hp L hL
    (dualPointFamily_class B hB stability p)
  have hqe := dualKernelCharacter_eq_of_family_class hA stability f hB q hq K hK
    (dualPointFamily_class B hB stability q)
  have hre := dualKernelCharacter_eq_of_family_class hA stability f hB r hr
    (RigidifiedLineBundle.tensor preservation L K) ht he
  rw [hpe, hqe, hre]
  exact trivialHomPullbackCharacter_rigidified_tensor f preservation L K hL hK

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)
local notation "beta" => dualKernelPointCharacter hA stability f hB preservation composition
  unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB

/-- Multiplication of actual dual-kernel points becomes addition of their intrinsic characters. -/
lemma dualKernelPointCharacter_mul {T : Over S}
    (x y : T ⟶ (GroupScheme.kernel df).X) :
    beta T (x * y) = beta T x + beta T y := by
  let := picardZeroClassesCommMonoid preservation unitCoherence associativity comparison
    symmetry B T
  let p := x ≫ (GroupScheme.kernelι df).hom.hom
  let q := y ≫ (GroupScheme.kernelι df).hom.hom
  have hc :
      dualPointClass stability B hB ((x * y) ≫ (GroupScheme.kernelι df).hom.hom) =
        picardZeroClassesTensor preservation B T
          (dualPointClass stability B hB p) (dualPointClass stability B hB q) := by
    have hi := congrArg Subtype.val ((kernelPointsEquiv df T).map_mul x y)
    change (x * y) ≫ (GroupScheme.kernelι df).hom.hom = p * q at hi
    rw [hi]
    exact (dualCommGroupSchemePointMulEquiv B hB preservation MB evaluationB stability
      composition unitCoherence associativity comparison symmetry T).map_mul p q
  change dualKernelCharacter hA stability f hB _ _ = _ + _
  exact dualKernelCharacter_tensor_of_class hA stability f hB preservation p q _ _ _ _ hc

/-- The actual dual-kernel identity determines the zero character. -/
@[simp]
lemma dualKernelPointCharacter_one (T : Over S) :
    beta T 1 = 0 := by
  have h := dualKernelPointCharacter_mul hA stability f hB preservation composition
    unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB
    (1 : T ⟶ (GroupScheme.kernel df).X) 1
  rw [one_mul] at h
  exact add_left_cancel (show beta T 1 + beta T 1 = beta T 1 + 0 by
    rw [← h, add_zero])

/-- The actual beta is an additive homomorphism from dual-kernel points. -/
def dualKernelPointCharacterAddHom (T : Over S) :
    Additive (T ⟶ (GroupScheme.kernel df).X) →+
      (Cartier.characters (kernelCommGroupScheme f)).obj (op T) where
  toFun x := beta T x.toMul
  map_zero' := dualKernelPointCharacter_one hA stability f hB preservation composition
    unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB T
  map_add' x y := dualKernelPointCharacter_mul hA stability f hB preservation composition
    unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB x.toMul y.toMul

/-- Inverting an actual dual-kernel point negates its intrinsic character. -/
@[simp]
lemma dualKernelPointCharacter_inv {T : Over S}
    (x : T ⟶ (GroupScheme.kernel df).X) :
    beta T x⁻¹ = -beta T x :=
  map_neg (dualKernelPointCharacterAddHom hA stability f hB preservation composition
    unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB T)
    (Additive.ofMul x)

end Langlands.AbelianScheme
