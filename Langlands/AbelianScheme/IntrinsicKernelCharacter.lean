import Langlands.AbelianScheme.KernelTranslationScalar
import Langlands.GroupScheme.Cartier.Characters

/-! # The actual intrinsic kernel character -/

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

/-- The actual scheme kernel, with its inherited commutativity. -/
def kernelCommGroupScheme : CommGroupScheme S :=
  { GroupScheme.kernel (groupHom f) with comm := inferInstance }

variable {T : Over S} {M : ((relativeSpace B.X.hom).obj T).Modules}
  (α : (Scheme.Modules.pullback ((homFamilySpaceMap f).app T)).obj M ≅
    structureModule ((relativeSpace A.X.hom).obj T))
  (h : UniversalGlobalFunctions A)

/-- The intrinsic kernel unit, as a homomorphism of actual groups of points. -/
def kernelTranslationUnitsHom {U : Over S} (a : U ⟶ T) :
    (U ⟶ (kernelCommGroupScheme f).X) →* Γ(U.left, ⊤)ˣ where
  toFun := kernelTranslationUnit f α h a
  map_one' := kernelTranslationUnit_one f α h a
  map_mul' := kernelTranslationUnit_mul f α h a

/-- The structural arrow of a scheme over `T`, regarded over `S`. -/
def kernelCharacterParameter (U : Over T.left) : (Over.map T.hom).obj U ⟶ T :=
  Over.homMk U.hom rfl

lemma kernelCharacterParameter_naturality {U V : Over T.left} (b : V ⟶ U) :
    (Over.map T.hom).map b ≫ kernelCharacterParameter (T := T) U =
      kernelCharacterParameter V := by
  ext
  exact Over.w b

/-- The kernel action gives a natural homomorphism from kernel points to actual Gm points. -/
def intrinsicKernelCharacterPoints (U : Over T.left) :
    (U ⟶ (Cartier.testBaseChange T (kernelCommGroupScheme f)).X) →*
      (U ⟶ (Gm T.left).X) :=
  (Gm.pointsEquiv T.left U).symm.toMonoidHom.comp
    ((kernelTranslationUnitsHom f α h (kernelCharacterParameter U)).comp
      (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U).toMonoidHom)

lemma intrinsicKernelCharacterPoints_naturality {U V : Over T.left} (b : V ⟶ U)
    (k : U ⟶ (Cartier.testBaseChange T (kernelCommGroupScheme f)).X) :
    intrinsicKernelCharacterPoints f α h V (b ≫ k) =
      b ≫ intrinsicKernelCharacterPoints f α h U k := by
  apply (Gm.pointsEquiv T.left V).injective
  simp only [intrinsicKernelCharacterPoints, MonoidHom.comp_apply,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply,
    Gm.pointsEquiv_naturality]
  change kernelTranslationUnit f α h (kernelCharacterParameter V)
      ((Over.map T.hom).map b ≫ baseChangePointsEquiv T.hom _ U k) =
    Units.map b.left.appTop.hom.toMonoidHom
      (kernelTranslationUnit f α h (kernelCharacterParameter U)
        (baseChangePointsEquiv T.hom _ U k))
  rw [← kernelCharacterParameter_naturality b, kernelTranslationUnit_precomp]
  rfl

/-- The actual homomorphism `ker(f)_T → Gm_T` induced by the transported kernel action. -/
def intrinsicKernelCharacterHom : Cartier.CharacterHom (kernelCommGroupScheme f) T :=
  Additive.ofMul (homOfPoints (intrinsicKernelCharacterPoints f α h)
    (intrinsicKernelCharacterPoints_naturality f α h))

/-- The intrinsic character as an element of the existing Cartier characters presheaf. -/
def intrinsicKernelCharacter : (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  (Cartier.characterHomEquiv (kernelCommGroupScheme f) T).symm
    (intrinsicKernelCharacterHom f α h)

@[simp]
lemma characterHomEquiv_intrinsicKernelCharacter :
    Cartier.characterHomEquiv (kernelCommGroupScheme f) T
        (intrinsicKernelCharacter f α h) = intrinsicKernelCharacterHom f α h :=
  AddEquiv.apply_symm_apply _ _

/-- On every test scheme over `T`, evaluation is the descended transported-action unit. -/
lemma intrinsicKernelCharacterHom_points (U : Over T.left)
    (k : U ⟶ (Cartier.testBaseChange T (kernelCommGroupScheme f)).X) :
    Gm.pointsEquiv T.left U (k ≫ (intrinsicKernelCharacterHom f α h).toMul.hom.hom) =
      kernelTranslationUnit f α h (kernelCharacterParameter U)
        (baseChangePointsEquiv T.hom (kernelCommGroupScheme f).toGrp U k) := by
  change Gm.pointsEquiv T.left U
    (k ≫ (homOfPoints (intrinsicKernelCharacterPoints f α h)
      (intrinsicKernelCharacterPoints_naturality f α h)).hom.hom) = _
  rw [comp_homOfPoints]
  exact (Gm.pointsEquiv T.left U).apply_symm_apply _

end Langlands.AbelianScheme
