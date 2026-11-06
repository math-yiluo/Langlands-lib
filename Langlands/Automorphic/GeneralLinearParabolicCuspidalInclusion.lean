import Langlands.Automorphic.GeneralLinearTwoBlockParabolic
import Langlands.Automorphic.GeneralLinearIntrinsicConstantTerm
import Langlands.Automorphic.GeneralLinearCuspidalComparison
import Langlands.Automorphic.GroupSchemeParabolicMeasure

/-! # Intrinsic all-parabolic GL cusp functions in the original cuspidal space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme
open Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance parabolicCuspidalComparisonIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance parabolicCuspidalComparisonSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (hPD : ParabolicDynamicStatement.{u})
  (hG : IsConnectedReductive
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
  [CompactSpace (AdeleQuotient F)]

/-- On an actual positive two-block proper parabolic, the intrinsic all-parabolic
vanishing condition is exactly the original matrix condition. -/
theorem hasVanishingNormalizedParabolicConstantTerm_generalLinearTwoBlock_iff
    {a b : ℕ} (h : a + b = n) (ha : 0 < a) (hb : 0 < b)
    (f : ContinuousRationalFunctions F GLG) :
    HasVanishingConstantTerm F GLG
        (properRationalParabolicRadicals hPD hG
          (generalLinearTwoBlockProperParabolic F h ha hb hPD))
        (properParabolicQuotientMeasure F GLG hPD hG
          (generalLinearTwoBlockProperParabolic F h ha hb hPD)) f ↔
      ∀ g : AdelicGL F n,
        Langlands.Automorphic.constantTerm F n h
          (continuousGeneralLinearEquiv F n f) g = 0 := by
  have hr :
      properRationalParabolicRadicals hPD hG
          (generalLinearTwoBlockProperParabolic F h ha hb hPD) = subgroup F h :=
    properRationalParabolicRadicals_generalLinearTwoBlock F h ha hb hPD hG
  have transport :
      ∀ (U : SubgroupFunctor GLG)
        [IsClosed (AdelicSubgroupPoints.adelicPoints F GLG U :
          Set (AdelicGroupPoints F GLG))],
        U = subgroup F h →
        (HasVanishingConstantTerm F GLG U
          (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG U) f ↔
          ∀ g : AdelicGL F n,
            Langlands.Automorphic.constantTerm F n h
              (continuousGeneralLinearEquiv F n f) g = 0) := by
    intro U hclosed heq
    subst U
    exact hasVanishingConstantTerm_generalLinearBlock_intrinsic_iff F h f
  exact transport _ hr

/-- All actual proper-parabolic vanishing implies the original standard-block
vanishing, with the same function and exact intrinsic normalization. -/
theorem normalizedGeneralLinearParabolicCuspidal_le_standardBlock :
    normalizedParabolicCuspidalSubrepresentation F GLG hPD hG ≤
      generalLinearStandardBlockVanishingSubrepresentation F n := by
  intro f hf
  rw [mem_generalLinearStandardBlockVanishingSubrepresentation_iff]
  intro a b h ha hb
  have hf' := (mem_parabolicCuspidalSubrepresentation F GLG hPD hG
    (properParabolicQuotientMeasure F GLG hPD hG) f).mp hf
  exact (hasVanishingNormalizedParabolicConstantTerm_generalLinearTwoBlock_iff
    F n hPD hG h ha hb f).mp
      (hf' (generalLinearTwoBlockProperParabolic F h ha hb hPD))

/-- Restrict the existing original-function comparison to the intrinsic
all-proper-parabolic cusp space. -/
def normalizedGeneralLinearParabolicCuspidalMap :
    (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule →ₗ[ℂ]
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toSubmodule :=
  (generalLinearCuspidalEquiv F n).toLinearMap.comp
    (Submodule.inclusion
      (normalizedGeneralLinearParabolicCuspidal_le_standardBlock F n hPD hG))

/-- The restriction loses no actual function. -/
theorem normalizedGeneralLinearParabolicCuspidalMap_injective :
    Function.Injective (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG) :=
  (generalLinearCuspidalEquiv F n).injective.comp (Submodule.inclusion_injective _)

@[simp]
theorem normalizedGeneralLinearParabolicCuspidalMap_val
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule) :
    (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG f).val =
      continuousGeneralLinearEquiv F n f.val := rfl

/-- Values are unchanged at corresponding actual adelic points. -/
theorem evaluate_normalizedGeneralLinearParabolicCuspidalMap
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG f).val
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) =
      evaluate F GLG f.val g :=
  evaluate_continuousGeneralLinearEquiv_at_point F n f.val g

/-- The actual full adelic positive right action intertwines the restricted map. -/
theorem normalizedGeneralLinearParabolicCuspidalMap_rightAction
    (f : (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toSubmodule)
    (g : AdelicGroupPoints F GLG) :
    normalizedGeneralLinearParabolicCuspidalMap F n hPD hG
        ((normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toRepresentation g f) =
      (Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)
        (normalizedGeneralLinearParabolicCuspidalMap F n hPD hG f) := by
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_rightAction F n f.val g

/-- Bundle the same injection with the exact full right-translation actions. -/
def normalizedGeneralLinearParabolicCuspidalIntertwiner :
    Representation.IntertwiningMap
      (normalizedParabolicCuspidalSubrepresentation F GLG hPD hG).toRepresentation
      ((Langlands.Automorphic.cuspidalSubrepresentation (K := F) (n := n)).toRepresentation.comp
        (GeneralLinearGroupPoints.adelicHomeomorph F n).toMonoidHom) where
  toLinearMap := normalizedGeneralLinearParabolicCuspidalMap F n hPD hG
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact normalizedGeneralLinearParabolicCuspidalMap_rightAction F n hPD hG f g

end Langlands.Automorphic.GroupSchemeFunctions
