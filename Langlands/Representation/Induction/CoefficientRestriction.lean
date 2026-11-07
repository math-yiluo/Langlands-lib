import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.CoefficientScalarRestriction

/-! Smooth induction and restriction of coefficient scalars on actual functions. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Induction

universe uR uG uV uW

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module R W] [Module ℂ W]
  [IsScalarTower ℂ R W]
  (P : Subgroup G) (σ : Representation ℂ P V) (τ : Representation R P W)
  (e : σ.Equiv (Jacquet.CoefficientRestriction.complexRepresentation τ))

local instance coefficientSmoothFunctionsComplexModule :
    Module ℂ (SmoothFunctions P τ) :=
  Module.compHom _ (algebraMap ℂ R)

local instance coefficientSmoothFunctionsComplexSMul :
    SMul ℂ (SmoothFunctions P τ) :=
  (coefficientSmoothFunctionsComplexModule P τ).toSMul

local instance coefficientSmoothFunctionsScalarTower :
    IsScalarTower ℂ R (SmoothFunctions P τ) :=
  IsScalarTower.of_compHom ℂ R _

/-- Postcomposition with the actual coefficient intertwiner, retaining a
single uniform right stabilizer for the whole induced function. -/
def coefficientSmoothFunction (f : SmoothFunctions P σ) : SmoothFunctions P τ := by
  refine ⟨⟨fun x => e (eval P σ f x), ?_⟩, ?_⟩
  · intro p x
    change e (f.1.1 ((p : G) * x)) = τ p (e (f.1.1 x))
    exact (congrArg e (f.1.property p x)).trans
      (LinearMap.congr_fun (e.isIntertwining' p) _)
  · obtain ⟨K, hK⟩ := f.property
    refine ⟨K, fun k => ?_⟩
    apply Subtype.ext
    funext x
    exact congrArg e (congrArg (fun a : EquivariantFunctions P σ => a.1 x) (hK k))

/-- The inverse is pointwise postcomposition with the inverse coefficient map. -/
def coefficientSmoothFunctionInv (f : SmoothFunctions P τ) : SmoothFunctions P σ := by
  refine ⟨⟨fun x => e.symm (eval P τ f x), ?_⟩, ?_⟩
  · intro p x
    change e.symm (f.1.1 ((p : G) * x)) = σ p (e.symm (f.1.1 x))
    exact (congrArg e.symm (f.1.property p x)).trans
      (LinearMap.congr_fun (e.symm.isIntertwining' p) _)
  · obtain ⟨K, hK⟩ := f.property
    refine ⟨K, fun k => ?_⟩
    apply Subtype.ext
    funext x
    exact congrArg e.symm (congrArg (fun a : EquivariantFunctions P τ => a.1 x) (hK k))

omit [IsTopologicalGroup G] in
@[simp] theorem coefficientSmoothFunction_eval (f : SmoothFunctions P σ) (x : G) :
    eval P τ (coefficientSmoothFunction P σ τ e f) x = e (eval P σ f x) := rfl

omit [IsTopologicalGroup G] in
@[simp] theorem coefficientSmoothFunctionInv_eval (f : SmoothFunctions P τ) (x : G) :
    eval P σ (coefficientSmoothFunctionInv P σ τ e f) x = e.symm (eval P τ f x) := rfl

/-- Restriction of scalars commutes with the actual full smooth induction,
through the given complex-linear equivalence on coefficient values. -/
def coefficientSmoothInducedEquiv :
    (smoothInduced P σ).Equiv
      (Jacquet.CoefficientRestriction.complexRepresentation (smoothInduced P τ)) :=
  Representation.Equiv.mk
    { toFun := coefficientSmoothFunction P σ τ e
      invFun := coefficientSmoothFunctionInv P σ τ e
      left_inv := by
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P σ (coefficientSmoothFunctionInv P σ τ e
          (coefficientSmoothFunction P σ τ e f)) x = eval P σ f x
        rw [coefficientSmoothFunctionInv_eval, coefficientSmoothFunction_eval,
          e.symm_apply_apply]
      right_inv := by
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P τ (coefficientSmoothFunction P σ τ e
          (coefficientSmoothFunctionInv P σ τ e f)) x = eval P τ f x
        rw [coefficientSmoothFunction_eval, coefficientSmoothFunctionInv_eval,
          e.apply_symm_apply]
      map_add' := by
        intro f g
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P τ (coefficientSmoothFunction P σ τ e (f + g)) x = _
        rw [coefficientSmoothFunction_eval]
        exact e.map_add _ _
      map_smul' := by
        intro c f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change eval P τ (coefficientSmoothFunction P σ τ e (c • f)) x =
          algebraMap ℂ R c • eval P τ (coefficientSmoothFunction P σ τ e f) x
        rw [coefficientSmoothFunction_eval, coefficientSmoothFunction_eval]
        change e.toLinearEquiv (c • eval P σ f x) =
          algebraMap ℂ R c • e.toLinearEquiv (eval P σ f x)
        rw [e.toLinearEquiv.map_smul, algebraMap_smul] }
    (by
      intro g
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change eval P τ (coefficientSmoothFunction P σ τ e (smoothInduced P σ g f)) x =
        eval P τ (coefficientSmoothFunction P σ τ e f) (x * g)
      rw [coefficientSmoothFunction_eval, coefficientSmoothFunction_eval]
      rfl)

end Langlands.Induction
