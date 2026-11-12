import Langlands.Global.AdelicWeilNormOneComparison
import Langlands.Global.NumberFieldAdeleTensorNorm
import Langlands.GroupScheme.AffineWeilCharacterNorm

/-! # Actual idele evaluation of transferred Weil norm characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The actual ground-field character obtained by restriction followed by determinant norm. -/
def normCharacter (χ : AlgebraicCharacter L G) :
    AlgebraicCharacter F (AffineWeil.groupScheme F L G) :=
  AffineWeil.normCharacter F L G χ

/-- Evaluation of a transferred character agrees exactly with the original full idele norm,
under the fixed canonical actual adelic Weil comparison. -/
theorem character_normCharacter_apply (χ : AlgebraicCharacter L G)
    (g : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    character F (AffineWeil.groupScheme F L G) (normCharacter F L G χ) g =
      AdelicFunctoriality.ideleNorm (K := F) (L := L)
        (character L G χ (adelicPointsEquiv F L G g)) := by
  change GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F)
    (CommAlgCat.of F (Adeles F))
      (g ≫ (AffineWeil.normCharacter F L G χ).hom.hom) = _
  rw [AffineWeil.normCharacter_affineUnits, numberFieldAdeleTensorNormUnits_eq]
  apply congrArg (AdelicFunctoriality.ideleNorm (K := F) (L := L))
  rw [adelicPointsEquiv_apply]
  exact (characterUnits_naturality L G χ
    (CommAlgCat.ofHom (numberFieldAdeleTensorMap F L))
    (AffineWeil.pointsEquiv F L G (Adeles F) g)).symm

/-- The equality is an identity of actual idele-valued group homomorphisms. -/
theorem character_normCharacter (χ : AlgebraicCharacter L G) :
    (character F (AffineWeil.groupScheme F L G) (normCharacter F L G χ)).toMonoidHom =
      (AdelicFunctoriality.ideleNorm (K := F) (L := L)).toMonoidHom.comp
        ((character L G χ).toMonoidHom.comp (adelicPointsEquiv F L G).toMonoidHom) := by
  apply MonoidHom.ext
  intro g
  exact character_normCharacter_apply F L G χ g

end Langlands.Global.AdelicWeilRestriction
