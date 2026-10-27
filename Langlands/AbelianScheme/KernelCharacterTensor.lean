import Langlands.AbelianScheme.KernelCharacterIndependence
import Langlands.AlgebraicGeometry.Modules.EqualCompositeTensor
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Tensor compatibility of the intrinsic kernel character -/

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

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} {M N : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (β : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj N ≅
    structureModule ((relativeSpace A.X.hom).obj T))

/-- Tensoring the actual trivializations composes the transported kernel actions. -/
lemma kernelTranslationAut_tensor {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationAut f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) a k =
      kernelTranslationAut f α a k ≪≫ kernelTranslationAut f β a k := by
  exact equalCompositeUnitAut_tensor preservation ((homFamilySpaceMap f).app T)
    ((relativeSpace A.X.hom).map a) (kernelShear f a k)
    (kernelShear_homFamilySpaceMap f a k).symm α β

/-- Tensoring the trivializations multiplies the actual transported-action scalars. -/
lemma kernelTranslationScalar_tensor {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) a k =
      kernelTranslationScalar f α a k * kernelTranslationScalar f β a k := by
  unfold kernelTranslationScalar
  rw [kernelTranslationAut_tensor, structureAutScalar_trans]

/-- The unique units on the parameter scheme multiply under tensor product. -/
lemma kernelTranslationUnit_tensor (h : UniversalGlobalFunctions A)
    {U : Over S} (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) h a k =
      kernelTranslationUnit f α h a k * kernelTranslationUnit f β h a k := by
  unfold kernelTranslationUnit
  rw [kernelTranslationScalar_tensor, map_mul]

/-- The actual group-scheme character of the tensor is the sum of the two characters. -/
lemma intrinsicKernelCharacterHom_tensor (h : UniversalGlobalFunctions A) :
    intrinsicKernelCharacterHom f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) h =
      intrinsicKernelCharacterHom f α h + intrinsicKernelCharacterHom f β h := by
  apply Additive.toMul.injective
  apply hom_ext_points
  intro U k
  apply (Gm.pointsEquiv T.left U).injective
  change Gm.pointsEquiv T.left U
      (k ≫ (intrinsicKernelCharacterHom f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) h).toMul.hom.hom) =
    Gm.pointsEquiv T.left U
      (k ≫ ((intrinsicKernelCharacterHom f α h).toMul *
        (intrinsicKernelCharacterHom f β h).toMul).hom.hom)
  simp only [Grp.Hom.hom_mul, Mon.Hom.hom_mul, MonObj.comp_mul, map_mul]
  rw [intrinsicKernelCharacterHom_points,
    intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points,
    kernelTranslationUnit_tensor]

/-- Tensor product becomes addition in the existing Cartier characters presheaf. -/
lemma intrinsicKernelCharacter_tensor (h : UniversalGlobalFunctions A) :
    intrinsicKernelCharacter f
        (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) α β) h =
      intrinsicKernelCharacter f α h + intrinsicKernelCharacter f β h := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).injective
  rw [(Cartier.characterHomEquiv (kernelCommGroupScheme f) T).map_add,
    characterHomEquiv_intrinsicKernelCharacter,
    characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter]
  exact intrinsicKernelCharacterHom_tensor preservation f α β h

/-- The tensor of two actual line bundles with trivial homomorphism pullback
again has trivial homomorphism pullback. -/
lemma hasTrivialHomPullback_tensor
    (L K : LineBundle ((relativeSpace B.X.hom).obj T))
    (hL : HasTrivialHomPullback f T L) (hK : HasTrivialHomPullback f T K) :
    HasTrivialHomPullback f T (LineBundle.tensor preservation L K) :=
  ⟨tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) hL.some hK.some⟩

/-- Tensor product on the actual category of line bundles with trivial
homomorphism pullback. -/
def trivialHomPullbackTensor (L K : TrivialHomPullbackFamily f T) :
    TrivialHomPullbackFamily f T :=
  ⟨LineBundle.tensor preservation L.obj K.obj,
    hasTrivialHomPullback_tensor preservation f L.obj K.obj L.property K.property⟩

/-- The choice-independent character of an actual line-bundle tensor is additive. -/
lemma trivialHomPullbackCharacter_tensor (h : UniversalGlobalFunctions A)
    (L K : LineBundle ((relativeSpace B.X.hom).obj T))
    (hL : HasTrivialHomPullback f T L) (hK : HasTrivialHomPullback f T K) :
    trivialHomPullbackCharacter f h (LineBundle.tensor preservation L K)
        (hasTrivialHomPullback_tensor preservation f L K hL hK) =
      trivialHomPullbackCharacter f h L hL + trivialHomPullbackCharacter f h K hK := by
  rw [trivialHomPullbackCharacter_eq f h (LineBundle.tensor preservation L K)
    (hasTrivialHomPullback_tensor preservation f L K hL hK)
    (tensorPullbackTrivialization preservation ((homFamilySpaceMap f).app T) hL.some hK.some)]
  exact intrinsicKernelCharacter_tensor preservation f hL.some hK.some h

end Langlands.AbelianScheme
