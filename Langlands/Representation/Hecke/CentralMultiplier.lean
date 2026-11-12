import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof
import Langlands.Representation.Smooth.RenardRegularHeckeProof
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Category.Abelian
import Mathlib.CategoryTheory.Center.Preadditive

/-! # Categorical central elements act as central Hecke multipliers -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  (hl : IsSmooth (HarmonicAnalysis.GroupAction.leftTests (G := G)))

/-- The universe-lifted left regular smooth representation. -/
def regularLift : SmoothRep.{0, u, max u v} ℂ G :=
  SmoothRep.universeLift.{v} (SmoothRep.of HarmonicAnalysis.GroupAction.leftTests hl)

/-- The integrated action on the lifted regular representation is actual convolution. -/
theorem regularLift_action (a b : HeckeAlgebra μ) :
    heckeAction μ (regularLift.{u,v} hl).representation (regularLift hl).isSmooth a
      (ULift.up (HeckeAlgebra.toTestFunction μ b)) =
        ULift.up (HeckeAlgebra.toTestFunction μ (a * b)) := by
  let E := SmoothRep.universeLiftEquiv.{v}
    (SmoothRep.of HarmonicAnalysis.GroupAction.leftTests hl)
  have h := integratedAction_intertwiner μ hl (regularLift.{u,v} hl).isSmooth
    E.toIntertwiningMap (HeckeAlgebra.toTestFunction μ a)
    (HeckeAlgebra.toTestFunction μ b)
  change ULift.up (heckeAction μ HarmonicAnalysis.GroupAction.leftTests hl a
      (HeckeAlgebra.toTestFunction μ b)) =
    heckeAction μ (regularLift.{u,v} hl).representation (regularLift hl).isSmooth a
      (ULift.up (HeckeAlgebra.toTestFunction μ b)) at h
  rw [Langlands.Renard.Smooth.leftRegularHeckeAction G μ hl] at h
  exact h.symm

local instance heckeFunctorEquivalence :
    (heckeNondegenerateModuleFunctor.{u, max u v} μ).IsEquivalence :=
  heckeNondegenerateModuleEquivalence G μ

/-- Evaluating the regular Hecke module on a vector, as an actual module map. -/
def regularEvaluationModule (V : SmoothRep.{0,u,max u v} ℂ G) (x : V) :
    heckeNondegenerateModule μ (regularLift.{u,v} hl) ⟶ heckeNondegenerateModule μ V :=
  ObjectProperty.homMk
    { toAddMonoidHom :=
        { toFun := fun b => heckeAction μ V.representation V.isSmooth
            ((HeckeAlgebra.toTestFunction μ).symm b.down) x
          map_zero' := by
            change heckeAction μ V.representation V.isSmooth 0 x = 0
            rw [map_zero]
            rfl
          map_add' := by
            intro a b
            change heckeAction μ V.representation V.isSmooth
              ((HeckeAlgebra.toTestFunction μ).symm (a.down + b.down)) x = _
            rw [map_add, map_add]
            rfl }
      map_smul' := by
        intro a b
        change heckeAction μ V.representation V.isSmooth
            ((HeckeAlgebra.toTestFunction μ).symm
              (heckeAction μ (regularLift.{u,v} hl).representation
                (regularLift hl).isSmooth a b).down) x = _
        obtain ⟨b⟩ := b
        have hb := regularLift_action.{u,v} μ hl a ((HeckeAlgebra.toTestFunction μ).symm b)
        change heckeAction μ (regularLift.{u,v} hl).representation (regularLift hl).isSmooth a
          (ULift.up b) = _ at hb
        rw [hb]
        exact congrArg (fun L => L x) (map_mul (heckeAction μ V.representation V.isSmooth) a
          ((HeckeAlgebra.toTestFunction μ).symm b)) }

/-- Evaluation is a smooth morphism by the published III.1.4 fullness theorem. -/
def regularEvaluation (V : SmoothRep.{0,u,max u v} ℂ G) (x : V) :
    regularLift.{u,v} hl ⟶ V :=
  (heckeNondegenerateModuleFunctor μ).preimage (regularEvaluationModule μ hl V x)

@[simp] theorem regularEvaluation_apply (V : SmoothRep.{0,u,max u v} ℂ G)
    (x : V) (a : HeckeAlgebra μ) :
    SmoothRep.hom (regularEvaluation μ hl V x)
      (ULift.up (HeckeAlgebra.toTestFunction μ a)) =
      heckeAction μ V.representation V.isSmooth a x := by
  have h := (heckeNondegenerateModuleFunctor μ).map_preimage
    (regularEvaluationModule μ hl V x)
  exact congrArg (fun k => NondegenerateEquivalence.underlying μ k (ULift.up (HeckeAlgebra.toTestFunction μ a))) h

/-- The Hecke-linear map given by right multiplication, on the lifted regular carrier. -/
def regularRightModule (b : HeckeAlgebra μ) :
    heckeNondegenerateModule μ (regularLift.{u,v} hl) ⟶
      heckeNondegenerateModule μ (regularLift.{u,v} hl) :=
  ObjectProperty.homMk
    { toAddMonoidHom :=
        { toFun := fun a => ULift.up (HeckeAlgebra.toTestFunction μ
            (((HeckeAlgebra.toTestFunction μ).symm a.down) * b))
          map_zero' := by
            change ULift.up (HeckeAlgebra.toTestFunction μ (0 * b)) = ULift.up 0
            rw [zero_mul, map_zero]
          map_add' := by
            intro a c
            apply ULift.ext
            change ((HeckeAlgebra.toTestFunction μ).symm (a.down + c.down)) * b =
              ((HeckeAlgebra.toTestFunction μ).symm a.down) * b +
                ((HeckeAlgebra.toTestFunction μ).symm c.down) * b
            rw [map_add, add_mul] }
      map_smul' := by
        intro a c
        obtain ⟨c⟩ := c
        change ULift.up (HeckeAlgebra.toTestFunction μ
          (((HeckeAlgebra.toTestFunction μ).symm
            (heckeAction μ (regularLift.{u,v} hl).representation
              (regularLift hl).isSmooth a (ULift.up c)).down) * b)) = _
        have hc := regularLift_action.{u,v} μ hl a ((HeckeAlgebra.toTestFunction μ).symm c)
        change heckeAction μ (regularLift.{u,v} hl).representation (regularLift hl).isSmooth a
          (ULift.up c) = _ at hc
        rw [hc]
        change ULift.up (HeckeAlgebra.toTestFunction μ ((a *
          ((HeckeAlgebra.toTestFunction μ).symm c)) * b)) = _
        rw [mul_assoc, ← regularLift_action μ hl]
        rfl }

/-- Right convolution as a morphism of the left regular smooth representation. -/
def regularRight (b : HeckeAlgebra μ) : regularLift.{u,v} hl ⟶ regularLift.{u,v} hl :=
  (heckeNondegenerateModuleFunctor μ).preimage (regularRightModule μ hl b)

@[simp] theorem regularRight_apply (a b : HeckeAlgebra μ) :
    SmoothRep.hom (regularRight.{u,v} μ hl b)
      (ULift.up (HeckeAlgebra.toTestFunction μ a)) =
        ULift.up (HeckeAlgebra.toTestFunction μ (a * b)) := by
  have h := (heckeNondegenerateModuleFunctor μ).map_preimage (regularRightModule.{u,v} μ hl b)
  exact congrArg (fun k => NondegenerateEquivalence.underlying μ k (ULift.up (HeckeAlgebra.toTestFunction μ a))) h

/-- A categorical central element, evaluated on the lifted left regular representation. -/
def centralMultiplier (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G)) :
    HeckeAlgebra μ →ₗ[ℂ] HeckeAlgebra μ :=
  (HeckeAlgebra.toTestFunction μ).symm.toLinearMap.comp
    (ULift.moduleEquiv.toLinearMap.comp
      ((SmoothRep.hom (z.app (regularLift.{u,v} hl))).toLinearMap.comp
        (ULift.moduleEquiv.symm.toLinearMap.comp (HeckeAlgebra.toTestFunction μ).toLinearMap)))

omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem centralMultiplier_up (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (a : HeckeAlgebra μ) :
    ULift.up (HeckeAlgebra.toTestFunction μ (centralMultiplier μ hl z a)) =
      SmoothRep.hom (z.app (regularLift.{u,v} hl))
        (ULift.up (HeckeAlgebra.toTestFunction μ a)) := rfl

/-- Central natural transformations are compatible with evaluation on every smooth vector. -/
theorem centralMultiplier_action (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (V : SmoothRep.{0,u,max u v} ℂ G) (a : HeckeAlgebra μ) (x : V) :
    heckeAction μ V.representation V.isSmooth (centralMultiplier μ hl z a) x =
      SmoothRep.hom (z.app V) (heckeAction μ V.representation V.isSmooth a x) := by
  have h := congrArg (fun k => SmoothRep.hom k
    (ULift.up (HeckeAlgebra.toTestFunction μ a)))
      (CatCenter.naturality z (regularEvaluation μ hl V x))
  change SmoothRep.hom (z.app V) (SmoothRep.hom (regularEvaluation μ hl V x) _) =
    SmoothRep.hom (regularEvaluation μ hl V x) (SmoothRep.hom (z.app (regularLift hl)) _) at h
  rw [regularEvaluation_apply, ← centralMultiplier_up, regularEvaluation_apply] at h
  exact h.symm

/-- Categorical centrality implies right-linearity of the multiplier. -/
theorem centralMultiplier_mul_left (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (a b : HeckeAlgebra μ) :
    centralMultiplier μ hl z (a * b) = centralMultiplier μ hl z a * b := by
  have h := congrArg (fun k => SmoothRep.hom k
    (ULift.up (HeckeAlgebra.toTestFunction μ a)))
      (CatCenter.naturality z (regularRight.{u,v} μ hl b))
  change SmoothRep.hom (z.app (regularLift hl)) (SmoothRep.hom (regularRight μ hl b) _) =
    SmoothRep.hom (regularRight μ hl b) (SmoothRep.hom (z.app (regularLift hl)) _) at h
  rw [regularRight_apply, ← centralMultiplier_up, ← centralMultiplier_up,
    regularRight_apply] at h
  exact congrArg (fun x => (HeckeAlgebra.toTestFunction μ).symm x.down) h

/-- Equivariance gives left-linearity of the multiplier. -/
theorem centralMultiplier_mul_right (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (a b : HeckeAlgebra μ) :
    centralMultiplier μ hl z (a * b) = a * centralMultiplier μ hl z b := by
  have h := integratedAction_intertwiner μ (regularLift.{u,v} hl).isSmooth
    (regularLift hl).isSmooth (SmoothRep.hom (z.app (regularLift hl)))
    (HeckeAlgebra.toTestFunction μ a) (ULift.up (HeckeAlgebra.toTestFunction μ b))
  change SmoothRep.hom (z.app (regularLift hl))
    (heckeAction μ (regularLift hl).representation (regularLift hl).isSmooth a _) =
    heckeAction μ (regularLift hl).representation (regularLift hl).isSmooth a _ at h
  rw [regularLift_action, ← centralMultiplier_up, ← centralMultiplier_up,
    regularLift_action] at h
  exact congrArg (fun x => (HeckeAlgebra.toTestFunction μ).symm x.down) h

omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem centralMultiplier_one (a : HeckeAlgebra μ) :
    centralMultiplier.{u,v} μ hl 1 a = a := rfl

omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem centralMultiplier_zero (a : HeckeAlgebra μ) :
    centralMultiplier.{u,v} μ hl 0 a = 0 := rfl

omit [T2Space G] [LocallyCompactSpace G] in
/-- Composition of central operators is composition of their Hecke multipliers. -/
theorem centralMultiplier_mul (z w : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (a : HeckeAlgebra μ) :
    centralMultiplier μ hl (z * w) a =
      centralMultiplier μ hl z (centralMultiplier μ hl w a) := rfl

/-- The multiplier can act on either side of the central operator on a smooth module. -/
theorem centralMultiplier_action_right (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (V : SmoothRep.{0,u,max u v} ℂ G) (a : HeckeAlgebra μ) (x : V) :
    heckeAction μ V.representation V.isSmooth (centralMultiplier μ hl z a) x =
      heckeAction μ V.representation V.isSmooth a (SmoothRep.hom (z.app V) x) := by
  rw [centralMultiplier_action]
  exact integratedAction_intertwiner μ V.isSmooth V.isSmooth
    (SmoothRep.hom (z.app V)) (HeckeAlgebra.toTestFunction μ a) x

/-- A central operator is the identity iff its multiplier acts identically on this module. -/
theorem central_app_eq_id_iff (z : CatCenter (SmoothRep.{0,u,max u v} ℂ G))
    (V : SmoothRep.{0,u,max u v} ℂ G) :
    z.app V = 𝟙 V ↔ ∀ (a : HeckeAlgebra μ) (x : V),
      heckeAction μ V.representation V.isSmooth (centralMultiplier μ hl z a) x =
        heckeAction μ V.representation V.isSmooth a x := by
  constructor
  · intro h a x
    rw [centralMultiplier_action, h]
    rfl
  · intro h
    apply ObjectProperty.hom_ext
    ext x
    obtain ⟨a, ha⟩ := heckeNonUnitalModule_isNondegenerate μ V.representation V.isSmooth x
    change heckeAction μ V.representation V.isSmooth (a : HeckeAlgebra μ) x = x at ha
    have hh := h (a : HeckeAlgebra μ) x
    rw [centralMultiplier_action, ha] at hh
    exact hh

end Langlands.Hecke
