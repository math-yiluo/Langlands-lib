import Langlands.AbelianScheme.KernelCharacterNaturality

/-! # Invariance of the kernel character under translation by image points -/

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

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} (c : T ⟶ A.X)

/-- The source shear by `c` lies over the target shear by the image point `f ∘ c`. -/
lemma shear_homFamilySpaceMap_id :
    (homFamilySpaceMap f).app T ≫ shear B (𝟙 T) (c ≫ (groupHom f).hom.hom) =
      shear A (𝟙 T) c ≫ (homFamilySpaceMap f).app T :=
  (shear_homFamilySpaceMap f (𝟙 T) c).symm

/-- Transport a homomorphism-pullback trivialization to the pullback along the
shear by an image point, through the source shear. -/
def shearPullbackTrivialization {M : ((relativeSpace B.X.hom).obj T).Modules}
    (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
      structureModule ((relativeSpace A.X.hom).obj T)) :
    (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj
        ((Scheme.Modules.pullback (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))).obj M) ≅
      structureModule ((relativeSpace A.X.hom).obj T) :=
  squarePullbackIso ((homFamilySpaceMap f).app T) ((homFamilySpaceMap f).app T)
      (shear A (𝟙 T) c) (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))
      (shear_homFamilySpaceMap_id f c) M ≪≫
    (Scheme.Modules.pullback (shear A (𝟙 T) c)).mapIso α ≪≫
      pullbackUnitIso (shear A (𝟙 T) c)

/-- Change of parameter followed by the source shear is a shear of the source
followed by the change of parameter. -/
lemma relativeSpace_map_shear_id {U : Over S} (a : U ⟶ T) :
    (relativeSpace A.X.hom).map a ≫ shear A (𝟙 T) c =
      shear A (𝟙 U) (a ≫ c) ≫ (relativeSpace A.X.hom).map a := by
  rw [← shear_one A a, shear_comp, shear_comp]
  simp

/-- Kernel translation commutes with the source shear, since `A` is commutative. -/
lemma kernelShear_shear_id {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelShear f a k ≫ shear A (𝟙 T) c =
      shear A (𝟙 U) (a ≫ c) ≫ kernelShear f a k := by
  rw [kernelShear, shear_comp, shear_comp]
  simp only [Category.comp_id, Category.id_comp]
  rw [mul_comm]

variable {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))

/-- The transported kernel action of the sheared trivialization is the pullback of the
original action along the source shear. -/
lemma kernelTranslationAut_shear {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationAut f (shearPullbackTrivialization f c α) a k =
      structureAutPullback (shear A (𝟙 U) (a ≫ c)) (kernelTranslationAut f α a k) := by
  have hab :
      ((relativeSpace A.X.hom).map a ≫ shear A (𝟙 T) c) ≫ (homFamilySpaceMap f).app T =
        (kernelShear f a k ≫ shear A (𝟙 T) c) ≫ (homFamilySpaceMap f).app T := by
    rw [Category.assoc, Category.assoc, ← shear_homFamilySpaceMap_id,
      ← Category.assoc, ← Category.assoc, kernelShear_homFamilySpaceMap]
  have e1 := equalCompositeUnitAut_square ((homFamilySpaceMap f).app T)
    ((homFamilySpaceMap f).app T) (shear A (𝟙 T) c)
    (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom)) (shear_homFamilySpaceMap_id f c) α
    ((relativeSpace A.X.hom).map a) (kernelShear f a k)
    (kernelShear_homFamilySpaceMap f a k).symm hab
  have e2 := equalCompositeUnitAut_precomp ((homFamilySpaceMap f).app T)
    ((relativeSpace A.X.hom).map a) (kernelShear f a k) α (shear A (𝟙 U) (a ≫ c))
    (kernelShear_homFamilySpaceMap f a k).symm
    (by simp only [Category.assoc, kernelShear_homFamilySpaceMap])
  simp only [relativeSpace_map_shear_id, kernelShear_shear_id] at e1
  rw [e2] at e1
  exact e1

/-- The global action scalar of the sheared trivialization is the original scalar. -/
lemma kernelTranslationScalar_shear {U : Over S} (a : U ⟶ T)
    (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f (shearPullbackTrivialization f c α) a k =
      Units.map (shear A (𝟙 U) (a ≫ c)).appTop.hom.toMonoidHom
        (kernelTranslationScalar f α a k) := by
  simp only [kernelTranslationScalar, kernelTranslationAut_shear, structureAutScalar_pullback]

/-- The descended unit of the sheared trivialization is the original descended unit. -/
lemma kernelTranslationUnit_shear (h : UniversalGlobalFunctions A) {U : Over S}
    (a : U ⟶ T) (k : U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationUnit f (shearPullbackTrivialization f c α) h a k =
      kernelTranslationUnit f α h a k := by
  unfold kernelTranslationUnit
  rw [kernelTranslationScalar_shear, relativeUnitDescend_map A h (𝟙 U)
    (shear A (𝟙 U) (a ≫ c)) (shear_fst A (𝟙 U) (a ≫ c))]
  rfl

/-- The intrinsic character of the sheared trivialization is the original character. -/
lemma intrinsicKernelCharacter_shear (h : UniversalGlobalFunctions A) :
    intrinsicKernelCharacter f (shearPullbackTrivialization f c α) h =
      intrinsicKernelCharacter f α h := by
  apply (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).injective
  rw [characterHomEquiv_intrinsicKernelCharacter, characterHomEquiv_intrinsicKernelCharacter]
  apply Additive.toMul.injective
  apply hom_ext_points
  intro U k
  apply (Gm.pointsEquiv T.left U).injective
  rw [intrinsicKernelCharacterHom_points, intrinsicKernelCharacterHom_points,
    kernelTranslationUnit_shear]

/-- Pullback along the shear by an image point preserves trivial homomorphism pullback. -/
lemma hasTrivialHomPullback_shear (L : LineBundle ((relativeSpace B.X.hom).obj T))
    (hL : HasTrivialHomPullback f T L) :
    HasTrivialHomPullback f T
      ((LineBundle.pullback (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))).obj L) :=
  ⟨shearPullbackTrivialization f c hL.some⟩

/-- Pullback along the shear by an image point preserves the canonical character. -/
lemma trivialHomPullbackCharacter_shear (h : UniversalGlobalFunctions A)
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    trivialHomPullbackCharacter f h
        ((LineBundle.pullback (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))).obj L)
        (hasTrivialHomPullback_shear f c L hL) =
      trivialHomPullbackCharacter f h L hL := by
  calc
    _ = intrinsicKernelCharacter f (shearPullbackTrivialization f c hL.some) h :=
      trivialHomPullbackCharacter_eq f h
        ((LineBundle.pullback (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))).obj L)
        (hasTrivialHomPullback_shear f c L hL)
        (shearPullbackTrivialization f c hL.some)
    _ = _ := intrinsicKernelCharacter_shear f c hL.some h

/-- If the class character is injective, pullback along the shear by an image point
preserves the isomorphism class of a line bundle with trivial homomorphism pullback. -/
theorem nonempty_shear_pullback_iso (h : UniversalGlobalFunctions A)
    (hinj : Function.Injective (trivialHomPullbackClassCharacter f (T := T) h))
    (L : LineBundle ((relativeSpace B.X.hom).obj T)) (hL : HasTrivialHomPullback f T L) :
    Nonempty ((LineBundle.pullback (shear B (𝟙 T) (c ≫ (groupHom f).hom.hom))).obj L ≅ L) := by
  have hq := hinj ((trivialHomPullbackClassCharacter_classOf f h _
    (hasTrivialHomPullback_shear f c L hL)).trans
      ((trivialHomPullbackCharacter_shear f c h L hL).trans
        (trivialHomPullbackClassCharacter_classOf f h L hL).symm))
  obtain ⟨e⟩ := Quotient.exact hq
  exact ⟨(trivialHomPullbackForget f T).mapIso e⟩

end Langlands.AbelianScheme
