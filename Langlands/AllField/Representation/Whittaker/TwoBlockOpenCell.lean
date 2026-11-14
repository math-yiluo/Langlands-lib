import Langlands.Representation.Whittaker.TwoBlockOpenCell
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# The concrete two-block cell of JPSS Proposition 9.1

For positive ranks `A = a + 1` and `B = b + 1`, the cell `P w U'` of `GL_(A+B)`,
the restriction of the literal ordered canonical normalized upper induction of
`(π₁, π₂)` to the representatives `w n(x)`, and the submodule of induced
functions supported in the cell with compactly supported restriction. These
are concrete definitions and elementary laws only.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockInducedCarrier hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear

universe uF uV

section Cell

variable (F : Type uF) [Field F] (a b : ℕ)

/-- The actual standard upper parabolic `P` of the ordered shape `(A, B)`. -/
abbrev twoBlockParabolic : Subgroup (Langlands.GeneralLinear (a + 1 + (b + 1)) F) :=
  (twoBlockShape a b).parabolic F

/-- The representative `w n(x)`: the all-positive block Weyl matrix times the
exchanged radical `U'(x)`, for `x` with `B` rows and `A` columns. -/
def twoBlockCellPoint (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
    Langlands.GeneralLinear (a + 1 + (b + 1)) F :=
  Shahidi.blockWeyl (a + 1) (b + 1) F *
    Shahidi.intertwiningUnipotent (a + 1) (b + 1) F x

/-- The cell `C = P w U'` of all products `q w n(x)` with `q ∈ P`. -/
def twoBlockCell : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F) :=
  {g | ∃ q : twoBlockParabolic F a b, ∃ x : Matrix (Fin (b + 1)) (Fin (a + 1)) F,
    g = (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F) *
      Shahidi.blockWeyl (a + 1) (b + 1) F *
        Shahidi.intertwiningUnipotent (a + 1) (b + 1) F x}

end Cell

section Induction

variable (F : Type uF) [Field F] (a b : ℕ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F) V₁)
  (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂)

/-- The literal ordered representation `ξ` of the parent statement. -/
abbrev twoBlockInduced [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :=
  (⟨⟩ : LocalFieldData F).normalizedProductInduced (twoBlockShape a b) (Shahidi.pairFamily π₁ π₂)

/-- The actual inducing representation of `P` on `V₁ ⊗ V₂`: the block tensor
through the Levi projection, twisted by the positive half modulus. -/
abbrev twoBlockInducingRepresentation [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    Representation ℂ (twoBlockParabolic F a b) (PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) :=
  twist ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (twoBlockShape a b))
    (((twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂)).comp
      ((twoBlockShape a b).leviProjection F))

/-- The carrier of `ξ`: the actual smooth covariant functions. -/
abbrev TwoBlockInducedCarrier [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (a + 1 + (b + 1))
  Induction.SmoothFunctions (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂)

/-- Evaluation of an element of the carrier of `ξ`, by `Induction.eval`. -/
def twoBlockEval [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : TwoBlockInducedCarrier F a b π₁ π₂)
    (g : Langlands.GeneralLinear (a + 1 + (b + 1)) F) :
    PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (a + 1 + (b + 1))
  Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂) f g

/-- The complex-linear restriction `f ↦ (x ↦ f(w n(x)))` to all tensor-valued
functions of `x`. -/
def twoBlockRestriction [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    TwoBlockInducedCarrier F a b π₁ π₂ →ₗ[ℂ]
      (Matrix (Fin (b + 1)) (Fin (a + 1)) F →
        PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) where
  toFun f x := twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The submodule `D`: induced functions whose support lies in the cell and
whose restriction to the representatives has compact support. -/
def twoBlockCellSubmodule [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Submodule ℂ (TwoBlockInducedCarrier F a b π₁ π₂) :=
  { carrier := {f | Function.support (twoBlockEval F a b π₁ π₂ f) ⊆ twoBlockCell F a b ∧
      HasCompactSupport (twoBlockRestriction F a b π₁ π₂ f)}
    zero_mem' := by
      refine ⟨fun g hg => (hg rfl).elim, ?_⟩
      rw [map_zero]
      exact HasCompactSupport.zero
    add_mem' := by
      rintro f h ⟨hf, hf'⟩ ⟨hh, hh'⟩
      refine ⟨(Function.support_add _ _).trans (Set.union_subset hf hh), ?_⟩
      rw [map_add]
      exact hf'.add hh'
    smul_mem' := by
      rintro c f ⟨hf, hf'⟩
      refine ⟨(Function.support_const_smul_subset c _).trans hf, ?_⟩
      rw [map_smul]
      exact hf'.mono (Function.support_const_smul_subset c _) }

/-- The injective linear inclusion `D → ξ`. -/
def twoBlockCellInclusion [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    twoBlockCellSubmodule F a b π₁ π₂ →ₗ[ℂ] TwoBlockInducedCarrier F a b π₁ π₂ :=
  (twoBlockCellSubmodule F a b π₁ π₂).subtype

@[simp] theorem twoBlockCellInclusion_apply [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : twoBlockCellSubmodule F a b π₁ π₂) :
    twoBlockCellInclusion F a b π₁ π₂ f = f.val :=
  rfl

/-- The restriction map on `D`. -/
def twoBlockCellRestriction [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    twoBlockCellSubmodule F a b π₁ π₂ →ₗ[ℂ]
      (Matrix (Fin (b + 1)) (Fin (a + 1)) F →
        PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂)) :=
  (twoBlockRestriction F a b π₁ π₂).comp (twoBlockCellInclusion F a b π₁ π₂)

/-- The restriction of an element of `D` has compact support. -/
theorem hasCompactSupport_twoBlockCellRestriction [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (f : twoBlockCellSubmodule F a b π₁ π₂) :
    HasCompactSupport (twoBlockCellRestriction F a b π₁ π₂ f) :=
  f.property.2

end Induction

end Langlands.AllField.Whittaker
