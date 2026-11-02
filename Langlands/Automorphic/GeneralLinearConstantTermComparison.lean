import Langlands.Global.GeneralLinearBlockUnipotentMeasure
import Langlands.Automorphic.GroupSchemeConstantTermConsequences

/-! # Actual two-block constant terms and the original general-linear integrals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

/-- Reconstruction in the original matrix group agrees with the actual subgroup inclusion. -/
theorem blockUnipotent_adelicCoordinates
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)) :
    Langlands.GeneralLinear.blockUnipotent h (adelicCoordinates F h x).toAdd =
      GeneralLinearGroupPoints.adelicHomeomorph F n x.val :=
  Langlands.GeneralLinear.blockUnipotent_coordinates_eq h
    (GroupScheme.GeneralLinear.twoBlockMatrixEquiv h (CommRingCat.of F)
      (CommAlgCat.of F (Adeles F)) x)

end Langlands.Global.GeneralLinearBlockUnipotent

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)
local notation "M" => Matrix (Fin a) (Fin b) (AdeleQuotient F)

local instance blockConstantTermGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- The actual integrand is exactly the original matrix integrand pulled back by the
proved quotient homeomorphism, for the original ambient function comparison. -/
theorem constantTermIntegrand_generalLinearBlock
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    constantTermIntegrand F GLG (subgroup F h) f g =
      Langlands.Automorphic.constantTermIntegrand F n h
        (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) ∘ quotientHomeomorph F h := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x =>
      change evaluate F GLG f (x.val * g) =
        Langlands.Automorphic.constantTermIntegrand F n h
          (continuousGeneralLinearEquiv F n f)
          (GeneralLinearGroupPoints.adelicHomeomorph F n g)
          (matrixQuotientMap (adelicCoordinates F h x).toAdd)
      rw [Langlands.Automorphic.constantTermIntegrand_mk,
        blockUnipotent_adelicCoordinates, ← map_mul,
        evaluate_continuousGeneralLinearEquiv_at_point]

local instance quotientMeasurableSpace : MeasurableSpace Q := borel Q
local instance quotientBorelSpace : BorelSpace Q := ⟨rfl⟩
local instance matrixMeasurableSpace : MeasurableSpace M := borel M
local instance matrixBorelSpace : BorelSpace M := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- Absolute Bochner integrability is preserved and reflected by the actual comparison. -/
theorem integrable_constantTermIntegrand_generalLinearBlock_iff
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    Integrable (constantTermIntegrand F GLG (subgroup F h) f g)
        (rationalQuotientMeasure F h) ↔
      Integrable (Langlands.Automorphic.constantTermIntegrand F n h
        (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)) (matrixQuotientHaar F a b) := by
  rw [constantTermIntegrand_generalLinearBlock]
  exact (measurePreserving_quotientHomeomorph F h).integrable_comp_emb
    (quotientHomeomorph F h).measurableEmbedding

/-- The original compact matrix convergence theorem proves convergence on the actual quotient. -/
theorem hasConvergentConstantTerm_generalLinearBlock
    (f : ContinuousRationalFunctions F GLG) :
    HasConvergentConstantTerm F GLG (subgroup F h) (rationalQuotientMeasure F h) f := by
  intro g
  exact (integrable_constantTermIntegrand_generalLinearBlock_iff F h f g).mpr
    (Langlands.Automorphic.integrable_constantTermIntegrand h
      (continuousGeneralLinearEquiv F n f) (GeneralLinearGroupPoints.adelicHomeomorph F n g))

/-- The normalized actual subgroup integral equals the original general-linear constant term. -/
theorem constantTerm_generalLinearBlock
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    constantTerm F GLG (subgroup F h) (rationalQuotientMeasure F h) f g =
      Langlands.Automorphic.constantTerm F n h (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) := by
  unfold constantTerm Langlands.Automorphic.constantTerm
  rw [constantTermIntegrand_generalLinearBlock]
  exact (measurePreserving_quotientHomeomorph F h).integral_comp
    (quotientHomeomorph F h).measurableEmbedding _

/-- The actual normalized block constant term is linear on the full continuous ambient space. -/
def generalLinearBlockConstantTermLinearMap :
    ContinuousRationalFunctions F GLG →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) :=
  compactConstantTermLinearMap F GLG (subgroup F h) (rationalQuotientMeasure F h)

theorem generalLinearBlockConstantTermLinearMap_apply
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    generalLinearBlockConstantTermLinearMap F h f g =
      Langlands.Automorphic.constantTerm F n h (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) :=
  constantTerm_generalLinearBlock F h f g

/-- Positive ambient right translation intertwines the actual integral operator. -/
theorem generalLinearBlockConstantTermLinearMap_rightAction
    (f : ContinuousRationalFunctions F GLG) (x g : AdelicGroupPoints F GLG) :
    generalLinearBlockConstantTermLinearMap F h (continuousRightAction F GLG x f) g =
      generalLinearBlockConstantTermLinearMap F h f (g * x) :=
  constantTerm_rightAction F GLG (subgroup F h) (rationalQuotientMeasure F h) f x g

/-- The actual subgroup acts trivially on the left argument of this normalized constant term. -/
theorem generalLinearBlockConstantTermLinearMap_subgroup_mul
    (f : ContinuousRationalFunctions F GLG)
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h))
    (g : AdelicGroupPoints F GLG) :
    generalLinearBlockConstantTermLinearMap F h f (x.val * g) =
      generalLinearBlockConstantTermLinearMap F h f g :=
  constantTerm_subgroup_mul F GLG (subgroup F h) (rationalQuotientMeasure F h)
    f x (measurePreserving_rightTranslate F h x) g

/-- Vanishing on the actual quotient is exactly vanishing of the original block constant term. -/
theorem hasVanishingConstantTerm_generalLinearBlock_iff
    (f : ContinuousRationalFunctions F GLG) :
    HasVanishingConstantTerm F GLG (subgroup F h) (rationalQuotientMeasure F h) f ↔
      ∀ g : AdelicGL F n, Langlands.Automorphic.constantTerm F n h
        (continuousGeneralLinearEquiv F n f) g = 0 := by
  constructor
  · intro hf g
    obtain ⟨g, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F n).surjective g
    rw [← constantTerm_generalLinearBlock]
    exact hf.2 g
  · intro hf
    refine ⟨hasConvergentConstantTerm_generalLinearBlock F h f, ?_⟩
    intro g
    rw [constantTerm_generalLinearBlock]
    exact hf _

end Langlands.Automorphic.GroupSchemeFunctions
