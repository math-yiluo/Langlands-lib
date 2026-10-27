import Langlands.AlgebraicGeometry.Picard.DualKernelPullback
import Langlands.AbelianScheme.KernelCharacterIndependence

/-! # The intrinsic character of an actual dual-kernel point -/

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
  {T : Over S} (p : T ⟶ dualScheme B hB)
  (hp : p ≫ dualSchemeMap homPicardZeroPullback f hA hB =
    (Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA)

/-- The actual bundle class supplied by the Poincaré representative of a dual-kernel point. -/
def dualKernelPullbackClass : TrivialHomPullbackClasses f T :=
  trivialHomPullbackClassOf f
    ((RigidifiedLineBundle.forget _).obj (dualPointFamily B hB p))
    ⟨dualKernelPullbackModuleIso hA stability f hB p hp⟩

/-- The intrinsic beta value, defined through actual trivial-pullback bundle classes. -/
def dualKernelCharacter : (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  trivialHomPullbackClassCharacter f (universalGlobalFunctions A)
    (dualKernelPullbackClass hA stability f hB p hp)

/-- Beta can be computed using every actual trivialization of the representative pullback. -/
lemma dualKernelCharacter_eq_intrinsic
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB p).obj.carrier ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    dualKernelCharacter hA stability f hB p hp =
      intrinsicKernelCharacter f α (universalGlobalFunctions A) :=
  trivialHomPullbackCharacter_eq f (universalGlobalFunctions A)
    ((RigidifiedLineBundle.forget _).obj (dualPointFamily B hB p))
    ⟨dualKernelPullbackModuleIso hA stability f hB p hp⟩ α

/-- Any isomorphic module representative with any actual trivialization computes the same beta. -/
lemma dualKernelCharacter_eq_of_iso
    {M : ((relativeSpace B.X.hom).obj T).Modules}
    (e : (dualPointFamily B hB p).obj.carrier ≅ M)
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    dualKernelCharacter hA stability f hB p hp =
      intrinsicKernelCharacter f α (universalGlobalFunctions A) := by
  rw [dualKernelCharacter_eq_intrinsic hA stability f hB p hp
    (dualKernelPullbackModuleIso hA stability f hB p hp)]
  exact intrinsicKernelCharacter_of_iso f
    (dualKernelPullbackModuleIso hA stability f hB p hp)
    (universalGlobalFunctions A) e α

/-- Every rigidified representative of the same Picard class gives the same character. -/
lemma dualKernelCharacter_eq_of_family_class
    (L : RigidifiedFamily B T)
    (hL : HasTrivialHomPullback f T ((RigidifiedLineBundle.forget _).obj L))
    (he : RigidifiedLineBundle.classOf B.X.hom (unitSection B) (unitSection_comp B) L =
      (dualPointClass stability B hB p).val) :
    dualKernelCharacter hA stability f hB p hp =
      trivialHomPullbackCharacter f (universalGlobalFunctions A)
        ((RigidifiedLineBundle.forget _).obj L) hL := by
  have hi : Nonempty (L ≅ dualPointFamily B hB p) := Quotient.exact he
  obtain ⟨e⟩ := hi
  exact trivialHomPullbackCharacter_of_iso f (universalGlobalFunctions A)
    ⟨dualKernelPullbackModuleIso hA stability f hB p hp⟩ hL
    ((RigidifiedLineBundle.forget _).mapIso e.symm)

/-- Beta interpreted as an actual homomorphism from the primal kernel over `T` to Gm. -/
def dualKernelCharacterHom : Cartier.CharacterHom (kernelCommGroupScheme f) T :=
  Cartier.characterHomEquiv (kernelCommGroupScheme f) T
    (dualKernelCharacter hA stability f hB p hp)

/-- Its homomorphism presentation is independent of the pullback trivialization. -/
lemma dualKernelCharacterHom_eq_intrinsic
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB p).obj.carrier ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    dualKernelCharacterHom hA stability f hB p hp =
      intrinsicKernelCharacterHom f α (universalGlobalFunctions A) := by
  rw [dualKernelCharacterHom, dualKernelCharacter_eq_intrinsic hA stability f hB p hp α,
    characterHomEquiv_intrinsicKernelCharacter]

/-- On all test schemes over `T`, beta evaluates to the descended transported-action unit. -/
lemma dualKernelCharacterHom_points
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB p).obj.carrier ≅
      structureModule ((relativeSpace A.X.hom).obj T))
    (U : Over T.left)
    (k : U ⟶ (Cartier.testBaseChange T (kernelCommGroupScheme f)).X) :
    Gm.pointsEquiv T.left U
        (k ≫ (dualKernelCharacterHom hA stability f hB p hp).toMul.hom.hom) =
      kernelTranslationUnit f α (universalGlobalFunctions A) (kernelCharacterParameter U)
        (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U k) := by
  rw [dualKernelCharacterHom_eq_intrinsic hA stability f hB p hp α,
    intrinsicKernelCharacterHom_points]

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

/-- Actual beta on every test scheme, from points of the scheme-theoretic dual kernel. -/
def dualKernelPointCharacter (T : Over S)
    (x : T ⟶ (GroupScheme.kernel df).X) :
    (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  dualKernelCharacter hA stability f hB
    (x ≫ (GroupScheme.kernelι df).hom.hom)
    (dualKernelPoint_eq_origin hA stability f hB preservation composition unitCoherence
      associativity comparison symmetry MA evaluationA MB evaluationB T x)

/-- Actual beta can be computed using any trivialization of its Poincaré representative. -/
lemma dualKernelPointCharacter_eq_intrinsic (T : Over S)
    (x : T ⟶ (GroupScheme.kernel df).X)
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        (dualPointFamily B hB (x ≫ (GroupScheme.kernelι df).hom.hom)).obj.carrier ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    dualKernelPointCharacter hA stability f hB preservation composition unitCoherence
        associativity comparison symmetry MA evaluationA MB evaluationB T x =
      intrinsicKernelCharacter f α (universalGlobalFunctions A) :=
  dualKernelCharacter_eq_intrinsic hA stability f hB _ _ α

end GroupKernel

end Langlands.AbelianScheme
