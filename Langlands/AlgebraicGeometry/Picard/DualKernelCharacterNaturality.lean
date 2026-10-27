import Langlands.AlgebraicGeometry.Picard.DualKernelCharacter
import Langlands.AbelianScheme.KernelCharacterNaturality

/-! # Test-scheme naturality of the actual dual-kernel character -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
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
  {T U : Over S} (b : U ⟶ T) (p : T ⟶ dualScheme B hB)
  (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
    (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)

/-- The actual Poincaré representative class pulls back to the representative
of the restricted dual point, without a chosen-trivialization equality. -/
lemma dualKernelPullbackClass_restrict :
    trivialHomPullbackClassesRestrict f b (dualKernelPullbackClass hA stability f hB p hp) =
      dualKernelPullbackClass hA stability f hB (b ≫ p)
        (dualKernelPoint_restrict hA f hB b p hp) := by
  unfold dualKernelPullbackClass
  rw [trivialHomPullbackClassesRestrict_classOf]
  exact trivialHomPullbackClassOf_eq_of_iso f _ _
    ((RigidifiedLineBundle.forget _).mapIso (dualPointFamilyPullbackIso B hB b p))

/-- The actual intrinsic beta commutes with every change of test scheme. -/
lemma dualKernelCharacter_restrict :
    dualKernelCharacter hA stability f hB (b ≫ p)
        (dualKernelPoint_restrict hA f hB b p hp) =
      (Cartier.characters (kernelCommGroupScheme f)).map b.op
        (dualKernelCharacter hA stability f hB p hp) := by
  unfold dualKernelCharacter
  rw [← dualKernelPullbackClass_restrict hA stability f hB b p hp]
  exact trivialHomPullbackClassCharacter_restrict f (universalGlobalFunctions A) b _

/-- The actual homomorphism presentation of beta restricts by Cartier pullback. -/
lemma dualKernelCharacterHom_restrict :
    dualKernelCharacterHom hA stability f hB (b ≫ p)
        (dualKernelPoint_restrict hA f hB b p hp) =
      Cartier.characterHomRestrict (kernelCommGroupScheme f) b
        (dualKernelCharacterHom hA stability f hB p hp) := by
  unfold dualKernelCharacterHom
  rw [dualKernelCharacter_restrict, Cartier.characterHomEquiv_restrict]

section GroupKernel

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
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

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)

/-- The point map on the actual scheme-theoretic dual kernel is natural. -/
lemma dualKernelPointCharacter_restrict (y : T ⟶ (GroupScheme.kernel df).X) :
    dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB U (b ≫ y) =
      (Cartier.characters (kernelCommGroupScheme f)).map b.op
        (dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
          associativity comparison symmetry MA evaluationA MB evaluationB T y) := by
  simpa only [dualKernelPointCharacter, Category.assoc] using
    dualKernelCharacter_restrict hA stability f hB b
      (y ≫ (GroupScheme.kernelι df).hom.hom)
      (dualKernelPoint_eq_origin hA stability f hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T y)

/-- Actual beta as a natural map from the representable dual-kernel point
functor to the existing relative Cartier-character functor. -/
def dualKernelPointCharacterNatTrans :
    yoneda.obj (GroupScheme.kernel df).X ⟶
      Cartier.characters (kernelCommGroupScheme f) ⋙ forget AddCommGrpCat.{u} where
  app T := TypeCat.ofHom
    (dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T.unop)
  naturality T U b := by
    ext y
    exact dualKernelPointCharacter_restrict hA stability f hB b.unop preservation composition
      unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB y

end GroupKernel

end Langlands.AbelianScheme
