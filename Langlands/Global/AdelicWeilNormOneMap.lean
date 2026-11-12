import Langlands.Global.AdelicWeilCharacterNorm
import Langlands.Global.AdelicWeilTopology
import Langlands.Global.IdeleNormAbsoluteValue

/-! # The canonical map on actual norm-one adelic Weil points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme AdelicGroupPoints

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of L)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The exact normalized norm of a transferred character on actual adelic points. -/
theorem characterNorm_normCharacter_apply (χ : AlgebraicCharacter L G)
    (g : AdelicGroupPoints F (AffineWeil.groupScheme F L G)) :
    characterNorm F (AffineWeil.groupScheme F L G) (normCharacter F L G χ) g =
      characterNorm L G χ (adelicPointsEquiv F L G g) := by
  change IdeleAbsoluteValue.full F
    (character F (AffineWeil.groupScheme F L G) (normCharacter F L G χ) g) = _
  rw [character_normCharacter_apply, AdelicFunctoriality.full_ideleNorm]
  rfl

/-- Ground-field norm-one points map into upper-field norm-one points. -/
theorem adelicPointsEquiv_mem_normOne
    (g : AdelicGroupPoints F (AffineWeil.groupScheme F L G))
    (hg : g ∈ normOneSubgroup F (AffineWeil.groupScheme F L G)) :
    adelicPointsEquiv F L G g ∈ normOneSubgroup L G := by
  rw [mem_normOneSubgroup] at hg ⊢
  intro χ
  rw [← characterNorm_normCharacter_apply]
  exact hg (normCharacter F L G χ)

/-- One inclusion for the full intersection of normalized character kernels. -/
theorem map_normOneSubgroup_le :
    (normOneSubgroup F (AffineWeil.groupScheme F L G)).map
      (adelicPointsEquiv F L G).toMonoidHom ≤ normOneSubgroup L G := by
  rintro _ ⟨g, hg, rfl⟩
  exact adelicPointsEquiv_mem_normOne F L G g hg

/-- Restriction of the fixed canonical adelic Weil map to the actual norm-one groups. -/
def normOneMap : normOneSubgroup F (AffineWeil.groupScheme F L G) →ₜ*
    normOneSubgroup L G where
  toMonoidHom :=
    (((adelicPointsEquiv F L G).toMonoidHom.comp
      (normOneSubgroup F (AffineWeil.groupScheme F L G)).subtype).codRestrict
        (normOneSubgroup L G) fun g => adelicPointsEquiv_mem_normOne F L G g g.property)
  continuous_toFun :=
    ((isHomeomorph_adelicPointsEquiv F L G).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem normOneMap_val
    (g : normOneSubgroup F (AffineWeil.groupScheme F L G)) :
    (normOneMap F L G g : AdelicGroupPoints L G) = adelicPointsEquiv F L G g := rfl

/-- The restricted map retains the injectivity of the canonical adelic equivalence. -/
theorem normOneMap_injective : Function.Injective (normOneMap F L G) := by
  intro g h he
  apply Subtype.ext
  apply (adelicPointsEquiv F L G).injective
  exact congrArg Subtype.val he

/-- The norm-one restriction is a closed embedding for the original subgroup topologies. -/
theorem isClosedEmbedding_normOneMap : Topology.IsClosedEmbedding (normOneMap F L G) := by
  exact ((isHomeomorph_adelicPointsEquiv F L G).isClosedEmbedding.comp
    (isClosed_normOneSubgroup F (AffineWeil.groupScheme F L G)).isClosedEmbedding_subtypeVal
      ).of_comp .subtypeVal

/-- Principal points are preserved by the restricted actual norm-one map. -/
@[simp] theorem normOneMap_rational
    (q : RationalGroupPoints F (AffineWeil.groupScheme F L G)) :
    normOneMap F L G (rationalNormOne F _ q) =
      rationalNormOne L G (rationalPointsEquiv F L G q) := by
  apply Subtype.ext
  exact adelicPointsEquiv_rational F L G q

end Langlands.Global.AdelicWeilRestriction
