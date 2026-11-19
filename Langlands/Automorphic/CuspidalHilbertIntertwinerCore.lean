import Langlands.Automorphic.CuspidalHilbertCoefficientComparison
import Langlands.Automorphic.CuspidalHilbertActionCompatibility
import Langlands.Automorphic.OperatorHilbertFormComparison

/-! # Adelic covariance for bounded extensions between form completions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.OperatorUnitaryFormCore

open Langlands.Global HilbertCoefficientComparison
universe u uV uW uX uY uM
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} {Y : Type uY} {M : Type uM} [Monoid M]
  {ρ : Representation ℂ (FiniteAdelicGL F n) V} {σ : Representation ℂ (FiniteAdelicGL F n) W}
  {κ : Representation ℂ (standardInfiniteCompact F n) V}
  {κ' : Representation ℂ (standardInfiniteCompact F n) W}
  {P : X → Module.End ℂ V} {Q : Y → Module.End ℂ W}
  {τ : Representation ℂ M V} {ξ : Representation ℂ M W}
  (b : OperatorUnitaryFormCore ρ κ P) (c : OperatorUnitaryFormCore σ κ' Q)
  (U : AdelicGL F n →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion))
  (U' : AdelicGL F n →* (c.HilbertCompletion →L[ℂ] c.HilbertCompletion))

/-- Every bounded extension of the given map on the original carriers
intertwines the two supplied adelic actions. -/
def BoundedExtensionsIntertwine (e : V →ₗ[ℂ] W) : Prop :=
  ∀ (L : b.HilbertCompletion →L[ℂ] c.HilbertCompletion),
    (∀ v, L (b.finiteForm.toHilbert v) = c.finiteForm.toHilbert (e v)) → AdelicIntertwines U U' L

/-- The finite and compact actions agree on the dense carriers by the
completed-action compatibility. The coefficients supply the remaining action. -/
theorem boundedExtensionsIntertwine_of_coefficients
    (D : ArchimedeanGL.EnvelopingAlgebra F n → V → V)
    (D' : ArchimedeanGL.EnvelopingAlgebra F n → W → W)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) b.finiteForm.toHilbert D)
    (hcoeff' : JointFiniteCoefficientLifts U' (AdelicGL.ofInfinite F n) c.finiteForm.toHilbert D')
    (hU : b.BoundedActionCompatibility U (AdelicGL.ofFinite F n)
      (fun k => AdelicGL.ofInfinite F n k.val))
    (hU' : c.BoundedActionCompatibility U' (AdelicGL.ofFinite F n)
      (fun k => AdelicGL.ofInfinite F n k.val))
    (e : V →ₗ[ℂ] W) (he : ∀ a v, e (D a v) = D' a (e v))
    (heK : ∀ k v, e (κ k v) = κ' k (e v)) (heF : ∀ d v, e (ρ d v) = σ d (e v)) :
    BoundedExtensionsIntertwine b c U U' e := by
  intro L hL
  refine adelicIntertwines_of_coefficients U U' b.finiteForm.toHilbert c.finiteForm.toHilbert
    b.finiteForm.denseRange_toHilbert D D' hcoeff hcoeff' L e hL he ?_ ?_
  · intro k v
    calc
      L (U (AdelicGL.ofInfinite F n k.val) (b.finiteForm.toHilbert v)) =
          L (b.completedCompactOperator k (b.finiteForm.toHilbert v)) :=
        congrArg L (hU.2 k _)
      _ = c.finiteForm.toHilbert (e (κ k v)) :=
        (congrArg L (b.completedCompactOperator_toHilbert k v)).trans (hL (κ k v))
      _ = c.finiteForm.toHilbert (κ' k (e v)) := congrArg c.finiteForm.toHilbert (heK k v)
      _ = c.completedCompactOperator k (c.finiteForm.toHilbert (e v)) :=
        (c.completedCompactOperator_toHilbert k (e v)).symm
      _ = U' (AdelicGL.ofInfinite F n k.val) (L (b.finiteForm.toHilbert v)) :=
        (hU'.2 k _).symm.trans (congrArg (U' (AdelicGL.ofInfinite F n k.val)) (hL v).symm)
  · intro d v
    calc
      L (U (AdelicGL.ofFinite F n d) (b.finiteForm.toHilbert v)) =
          L (b.completedFiniteOperator d (b.finiteForm.toHilbert v)) :=
        congrArg L (hU.1 d _)
      _ = c.finiteForm.toHilbert (e (ρ d v)) :=
        (congrArg L (b.completedFiniteOperator_toHilbert d v)).trans (hL (ρ d v))
      _ = c.finiteForm.toHilbert (σ d (e v)) := congrArg c.finiteForm.toHilbert (heF d v)
      _ = c.completedFiniteOperator d (c.finiteForm.toHilbert (e v)) :=
        (c.completedFiniteOperator_toHilbert d (e v)).symm
      _ = U' (AdelicGL.ofFinite F n d) (L (b.finiteForm.toHilbert v)) :=
        (hU'.1 d _).symm.trans (congrArg (U' (AdelicGL.ofFinite F n d)) (hL v).symm)

/-- A continuous equivalence extends the original full operator equivalence
with a positive ratio of the two forms and intertwines all adelic operators. -/
def AdelicHilbertFormComparison (e : τ.Equiv ξ) : Prop :=
  ∃ (a : ℝ) (E : b.HilbertCompletion ≃L[ℂ] c.HilbertCompletion),
    0 < a ∧ (∀ v, E (b.finiteForm.toHilbert v) = c.finiteForm.toHilbert (e v)) ∧
    (∀ x y, Inner.inner ℂ (E x) (E y) = (a : ℂ) * Inner.inner ℂ x y) ∧
    AdelicIntertwines U U' E.toContinuousLinearMap

/-- The same extension and positive ratio from form comparison satisfy the
full covariance as soon as bounded extensions have that covariance. -/
theorem adelicHilbertFormComparison_of_extensions (e : τ.Equiv ξ)
    (hcompare : HilbertFormComparison b c e)
    (hcov : BoundedExtensionsIntertwine b c U U' e.toIntertwiningMap.toLinearMap) :
    AdelicHilbertFormComparison b c U U' e := by
  obtain ⟨a, E, ha, hE, hinner, _, _⟩ := hcompare
  exact ⟨a, E, ha, hE, hinner, hcov E.toContinuousLinearMap hE⟩

/-- An adelic action on the completion of a supplied form, with its
joint-finite coefficient and completed-operator comparisons. -/
structure AdelicCompletion where
  action : AdelicGL F n →* (b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
  differential : ArchimedeanGL.EnvelopingAlgebra F n → V → V
  coefficients : JointFiniteCoefficientLifts action (AdelicGL.ofInfinite F n)
    b.finiteForm.toHilbert differential
  boundedCompatibility : b.BoundedActionCompatibility action (AdelicGL.ofFinite F n)
    (fun k => AdelicGL.ofInfinite F n k.val)

/-- Positive form comparison and covariance of the original operators
give full covariance of the same extended equivalence. -/
theorem AdelicCompletion.formComparison
    (A : AdelicCompletion b) (B : AdelicCompletion c) (e : τ.Equiv ξ)
    (hcompare : HilbertFormComparison b c e)
    (he : ∀ a v, e (A.differential a v) = B.differential a (e v))
    (heK : ∀ k v, e (κ k v) = κ' k (e v)) (heF : ∀ d v, e (ρ d v) = σ d (e v)) :
    AdelicHilbertFormComparison b c A.action B.action e :=
  adelicHilbertFormComparison_of_extensions b c A.action B.action e hcompare
    (boundedExtensionsIntertwine_of_coefficients b c A.action B.action A.differential B.differential
      A.coefficients B.coefficients A.boundedCompatibility B.boundedCompatibility
      e.toIntertwiningMap.toLinearMap he heK heF)

end Langlands.Automorphic.OperatorUnitaryFormCore
