import Langlands.AbelianScheme.KernelPairFactorization
import Langlands.AbelianScheme.TrivialPullbackCharacterInjectiveStatement
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentUniquenessProof

/-! # Injectivity of the normalized character from descent of isomorphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S} (f : A ⟶ B)
  {T : Over S} {M N : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (β : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj N ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (h : UniversalGlobalFunctions A)

/-- Equal intrinsic characters give equal kernel-translation scalars. -/
lemma kernelTranslationScalar_eq_of_character_eq
    (hχ : intrinsicKernelCharacter f α h = intrinsicKernelCharacter f β h)
    (U : Over T.left) (k : (Over.map T.hom).obj U ⟶ (GroupScheme.kernel (groupHom f)).X) :
    kernelTranslationScalar f α (kernelCharacterParameter U) k =
      kernelTranslationScalar f β (kernelCharacterParameter U) k := by
  have hhom : intrinsicKernelCharacterHom f α h = intrinsicKernelCharacterHom f β h := by
    rw [← characterHomEquiv_intrinsicKernelCharacter, hχ,
      characterHomEquiv_intrinsicKernelCharacter]
  let k' := (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U).symm k
  have hα := intrinsicKernelCharacterHom_points f α h U k'
  have hβ := intrinsicKernelCharacterHom_points f β h U k'
  rw [hhom, hβ] at hα
  simp only [k', MulEquiv.apply_symm_apply] at hα
  rw [← relativeUnitsPullback_kernelTranslationUnit f α h,
    ← relativeUnitsPullback_kernelTranslationUnit f β h, hα]

/-- Equal intrinsic characters give equal comparison scalars on every pair of maps with
equal composite along `f_T`. -/
lemma equalCompositeScalar_eq_of_character_eq
    (hχ : intrinsicKernelCharacter f α h = intrinsicKernelCharacter f β h)
    {U : Scheme.{u}} (a b : U ⟶ (relativeSpace A.X.hom).obj T)
    (hab : a ≫ (homFamilySpaceMap f).app T = b ≫ (homFamilySpaceMap f).app T) :
    structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T) a b hab α) =
      structureAutScalar (equalCompositeUnitAut ((homFamilySpaceMap f).app T) a b hab β) := by
  rw [structureAutScalar_equalCompositeUnitAut_eq, structureAutScalar_equalCompositeUnitAut_eq,
    kernelTranslationScalar_eq_of_character_eq f α β h hχ]

/-- Descent of isomorphisms along the faithfully flat `f_T` gives injectivity. -/
theorem trivialPullbackCharacterInjective_of_uniqueness
    (hU : UnitCocycleDescentUniquenessStatement.{u}) :
    TrivialPullbackCharacterInjectiveStatement.{u} := by
  intro S A B f hf T x y
  refine Quotient.inductionOn₂ x y fun L K hLK => ?_
  obtain ⟨α⟩ := L.property
  obtain ⟨β⟩ := K.property
  have hχ : intrinsicKernelCharacter f α (universalGlobalFunctions A) =
      intrinsicKernelCharacter f β (universalGlobalFunctions A) := by
    rw [← trivialHomPullbackCharacter_eq f _ L.obj L.property α,
      ← trivialHomPullbackCharacter_eq f _ K.obj K.property β]
    exact hLK
  have := isFinite_homFamilySpaceMap hf T
  obtain ⟨e⟩ := hU _ _ ((homFamilySpaceMap f).app T) inferInstance
    (flat_homFamilySpaceMap hf T) (surjective_homFamilySpaceMap hf T) L.obj K.obj α β
    (fun _ a b hab ↦ equalCompositeScalar_eq_of_character_eq f α β _ hχ a b hab)
  exact Quotient.sound ⟨ObjectProperty.isoMk _ e⟩

/-- The normalized character of trivial-pullback classes is injective. -/
theorem trivialPullbackCharacterInjective : TrivialPullbackCharacterInjectiveStatement.{u} :=
  trivialPullbackCharacterInjective_of_uniqueness unitCocycleDescentUniqueness

end Langlands.AbelianScheme
