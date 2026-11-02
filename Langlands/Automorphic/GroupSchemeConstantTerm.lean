import Langlands.Global.AdelicSubgroupQuotient
import Langlands.Automorphic.GroupSchemeFiniteLevel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Constant-term descent and explicit convergence on actual subgroup quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (U : GroupScheme.SubgroupFunctor G)

/-- The actual function `n ↦ f(n*g)` descends through the principal subgroup image. -/
def constantTermIntegrand (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) :
    AdelicSubgroupPoints.RationalQuotient F G U → ℂ :=
  LeftCosetSpace.lift (AdelicSubgroupPoints.rationalSubgroup F G U)
    (fun n => evaluate F G f ((n : AdelicGroupPoints F G) * g)) (by
      rintro ⟨_, q, rfl⟩ n
      change f.val.val ((AdelicGroupPoints.rational F G q.val *
        (n : AdelicGroupPoints F G)) * g) = _
      rw [mul_assoc]
      exact f.val.property q.val _)

@[simp]
theorem constantTermIntegrand_mk (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) (n : AdelicSubgroupPoints.adelicPoints F G U) :
    constantTermIntegrand F G U f g
      (LeftCosetSpace.mk (AdelicSubgroupPoints.rationalSubgroup F G U) n) =
        evaluate F G f ((n : AdelicGroupPoints F G) * g) := rfl

theorem continuous_constantTermIntegrand (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) : Continuous (constantTermIntegrand F G U f g) := by
  apply (LeftCosetSpace.continuous_iff
    (AdelicSubgroupPoints.rationalSubgroup F G U)).mpr
  exact f.property.comp (continuous_subtype_val.mul continuous_const)

/-- For fixed ambient `g`, descent is complex linear in the original continuous function. -/
def constantTermIntegrandLinearMap (g : AdelicGroupPoints F G) :
    ContinuousRationalFunctions F G →ₗ[ℂ]
      (AdelicSubgroupPoints.RationalQuotient F G U → ℂ) where
  toFun f := constantTermIntegrand F G U f g
  map_add' f h := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n => rfl
  map_smul' c f := by
    funext q
    induction q using Quotient.inductionOn with
    | _ n => rfl

theorem constantTermIntegrand_rightAction (f : ContinuousRationalFunctions F G)
    (h g : AdelicGroupPoints F G) :
    constantTermIntegrand F G U (continuousRightAction F G h f) g =
      constantTermIntegrand F G U f (g * h) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ n => exact congrArg (evaluate F G f) (mul_assoc _ _ _)

variable [MeasurableSpace (AdelicSubgroupPoints.RationalQuotient F G U)]
  (mu : Measure (AdelicSubgroupPoints.RationalQuotient F G U))

/-- Absolute Bochner convergence at every actual adelic argument, kept separate from integration. -/
def HasConvergentConstantTerm (f : ContinuousRationalFunctions F G) : Prop :=
  ∀ g : AdelicGroupPoints F G, Integrable (constantTermIntegrand F G U f g) mu

/-- The totalized integral; additivity is asserted only on its convergent domain. -/
def constantTerm (f : ContinuousRationalFunctions F G) (g : AdelicGroupPoints F G) : ℂ :=
  ∫ q, constantTermIntegrand F G U f g q ∂mu

/-- Functions with convergent subgroup constant terms form an actual subrepresentation. -/
def convergentConstantTermSubrepresentation : Subrepresentation (continuousRightAction F G) where
  toSubmodule :=
    { carrier := {f | HasConvergentConstantTerm F G U mu f}
      zero_mem' := by
        intro g
        change Integrable (constantTermIntegrandLinearMap F G U g 0) mu
        rw [map_zero]
        exact integrable_zero _ _ _
      add_mem' := by
        intro f h hf hh g
        change Integrable (constantTermIntegrandLinearMap F G U g (f + h)) mu
        rw [map_add]
        exact (hf g).add (hh g)
      smul_mem' := by
        intro c f hf g
        change Integrable (constantTermIntegrandLinearMap F G U g (c • f)) mu
        rw [map_smul]
        exact (hf g).smul c }
  apply_mem_toSubmodule h f hf g := by
    rw [constantTermIntegrand_rightAction]
    exact hf (g * h)

/-- The actual domain on which the constant-term operator is complex linear. -/
abbrev ConvergentConstantTermFunctions :=
  (convergentConstantTermSubrepresentation F G U mu).toSubmodule

/-- Positive right translation restricted to the convergent domain. -/
def convergentConstantTermRightAction :
    Representation ℂ (AdelicGroupPoints F G) (ConvergentConstantTermFunctions F G U mu) :=
  (convergentConstantTermSubrepresentation F G U mu).toRepresentation

theorem constantTerm_zero (g : AdelicGroupPoints F G) :
    constantTerm F G U mu 0 g = 0 := by
  change (∫ q, constantTermIntegrandLinearMap F G U g 0 q ∂mu) = 0
  rw [map_zero]
  exact integral_zero _ _

theorem constantTerm_add (f h : ContinuousRationalFunctions F G)
    (hf : HasConvergentConstantTerm F G U mu f)
    (hh : HasConvergentConstantTerm F G U mu h) (g : AdelicGroupPoints F G) :
    constantTerm F G U mu (f + h) g =
      constantTerm F G U mu f g + constantTerm F G U mu h g := by
  change (∫ q, constantTermIntegrandLinearMap F G U g (f + h) q ∂mu) = _
  rw [map_add]
  exact integral_add (hf g) (hh g)

theorem constantTerm_smul (c : ℂ) (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) :
    constantTerm F G U mu (c • f) g = c • constantTerm F G U mu f g := by
  change (∫ q, constantTermIntegrandLinearMap F G U g (c • f) q ∂mu) = _
  rw [map_smul]
  exact integral_smul c _

theorem constantTerm_rightAction (f : ContinuousRationalFunctions F G)
    (h g : AdelicGroupPoints F G) :
    constantTerm F G U mu (continuousRightAction F G h f) g =
      constantTerm F G U mu f (g * h) := by
  unfold constantTerm
  rw [constantTermIntegrand_rightAction]

/-- The integral gives a complex linear function-valued map on the proven convergence domain. -/
def constantTermLinearMap :
    ConvergentConstantTermFunctions F G U mu →ₗ[ℂ] (AdelicGroupPoints F G → ℂ) where
  toFun f := constantTerm F G U mu f.val
  map_add' f h := by
    funext g
    exact constantTerm_add F G U mu f.val h.val f.property h.property g
  map_smul' c f := by
    funext g
    exact constantTerm_smul F G U mu c f.val g

theorem constantTermLinearMap_rightAction (f : ConvergentConstantTermFunctions F G U mu)
    (h g : AdelicGroupPoints F G) :
    constantTermLinearMap F G U mu (convergentConstantTermRightAction F G U mu h f) g =
      constantTermLinearMap F G U mu f (g * h) :=
  constantTerm_rightAction F G U mu f.val h g

/-- Measure rescaling changes the totalized constant term by the corresponding real scalar. -/
theorem constantTerm_smul_measure (c : ℝ≥0∞) (f : ContinuousRationalFunctions F G)
    (g : AdelicGroupPoints F G) :
    constantTerm F G U (c • mu) f g = c.toReal • constantTerm F G U mu f g :=
  integral_smul_measure _ c

end Langlands.Automorphic.GroupSchemeFunctions
