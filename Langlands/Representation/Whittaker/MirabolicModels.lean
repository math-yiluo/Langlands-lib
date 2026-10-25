import Langlands.Group.GL.Mirabolic
import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.Representation.Induction.Definitions

/-! # Standard smooth and compact Whittaker induction on the mirabolic group -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis
open scoped BigOperators

universe uF

variable {F : Type uF} [CommRing F] [TopologicalSpace F]

/-- The published standard character transported to the actual subgroup of the mirabolic group. -/
def mirabolicCharacter (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Mirabolic.upperUnipotent n F →* ℂˣ :=
  (standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom

@[simp] theorem mirabolicCharacter_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : Mirabolic.upperUnipotent n F) :
    mirabolicCharacter ψ n g = standardCharacter ψ n (Mirabolic.upperUnipotentEquiv g) := rfl

/-- The exact product of adjacent-entry characters used by the Kirillov statement. -/
theorem mirabolicCharacter_eq_product (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : Mirabolic.upperUnipotent n F) :
    (mirabolicCharacter ψ n g : ℂ) =
      ∏ i : Fin n, ψ.complex (g.val.val.val i.castSucc i.succ) :=
  standardCharacter_eq_product ψ (Mirabolic.upperUnipotentEquiv g)

@[simp] theorem mirabolicCharacter_rankOne (ψ : UnitaryAdditiveCharacter F) :
    mirabolicCharacter ψ 0 = 1 := by
  ext g
  simp

/-- The actual scalar representation attached to the standard character. -/
def mirabolicCharacterRepresentation (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (Mirabolic.upperUnipotent n F) ℂ :=
  characterRepresentation (mirabolicCharacter ψ n)

@[simp] theorem mirabolicCharacterRepresentation_apply
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : Mirabolic.upperUnipotent n F) (z : ℂ) :
    mirabolicCharacterRepresentation ψ n g z = (mirabolicCharacter ψ n g : ℂ) * z := rfl

variable [IsTopologicalRing F]

/-- Continuity is inherited from the published character and the subgroup identification. -/
def mirabolicCharacterContinuous (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    ContinuousMonoidHom (Mirabolic.upperUnipotent n F) ℂˣ where
  toMonoidHom := mirabolicCharacter ψ n
  continuous_toFun := (standardCharacterContinuous ψ n).continuous.comp
    Mirabolic.upperUnipotentContinuousEquiv.continuous

/-- Smooth covariant complex-valued functions on the actual mirabolic group. -/
abbrev MirabolicSmoothFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : Type uF :=
  Induction.SmoothFunctions (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n)

/-- The standard smooth induced representation on the mirabolic group. -/
abbrev mirabolicSmoothInduced (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (mirabolic n F) (MirabolicSmoothFunctions ψ n) :=
  Induction.smoothInduced (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n)

/-- Evaluate the underlying actual function. -/
def mirabolicEval (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicSmoothFunctions ψ n) (g : mirabolic n F) : ℂ :=
  Induction.eval (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n) f g

omit [IsTopologicalRing F] in
@[simp] theorem mirabolicEval_def (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicSmoothFunctions ψ n) (g : mirabolic n F) :
    mirabolicEval ψ n f g = f.val.val g := rfl

/-- Evaluation after right translation. -/
@[simp] theorem mirabolicEval_translate (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicSmoothFunctions ψ n) (s g : mirabolic n F) :
    mirabolicEval ψ n (mirabolicSmoothInduced ψ n s f) g =
      mirabolicEval ψ n f (g * s) := rfl

omit [IsTopologicalRing F] in
/-- Covariance with the actual unipotent subgroup and its transported character. -/
theorem mirabolicEval_covariance (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicSmoothFunctions ψ n) (u : Mirabolic.upperUnipotent n F)
    (g : mirabolic n F) :
    mirabolicEval ψ n f (u.val * g) =
      (mirabolicCharacter ψ n u : ℂ) * mirabolicEval ψ n f g :=
  f.val.property u g

omit [IsTopologicalRing F] in
/-- Covariance in the exact adjacent-entry product convention. -/
theorem mirabolicEval_covariance_product (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicSmoothFunctions ψ n) (u : Mirabolic.upperUnipotent n F)
    (g : mirabolic n F) :
    mirabolicEval ψ n f (u.val * g) =
      (∏ i : Fin n, ψ.complex (u.val.val.val i.castSucc i.succ)) * mirabolicEval ψ n f g := by
  rw [mirabolicEval_covariance, mirabolicCharacter_eq_product]

/-- The compact-support subrepresentation is literally inside the smooth model. -/
abbrev mirabolicCompactSubrepresentation (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Subrepresentation (mirabolicSmoothInduced ψ n) :=
  Induction.compactSubrepresentation (Mirabolic.upperUnipotent n F)
    (mirabolicCharacterRepresentation ψ n)

/-- Membership means compactness of the actual projected nonzero support in `U \ P`. -/
@[simp] theorem mem_mirabolicCompactSubrepresentation
    (ψ : UnitaryAdditiveCharacter F) (n : ℕ) (f : MirabolicSmoothFunctions ψ n) :
    f ∈ mirabolicCompactSubrepresentation ψ n ↔
      IsCompact (Induction.quotientSupport (Mirabolic.upperUnipotent n F)
        (mirabolicEval ψ n f)) := Iff.rfl

/-- Compactly induced functions retain the natural field universe. -/
abbrev MirabolicCompactFunctions (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : Type uF :=
  Induction.CompactFunctions (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n)

/-- Compact induction with the same scalar character and right translation. -/
abbrev mirabolicCompactInduced (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Representation ℂ (mirabolic n F) (MirabolicCompactFunctions ψ n) :=
  Induction.compactInduced (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n)

/-- The canonical equivariant inclusion into the standard smooth induced model. -/
abbrev mirabolicCompactInclusion (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n) :=
  Induction.compactInclusion (Mirabolic.upperUnipotent n F) (mirabolicCharacterRepresentation ψ n)

@[simp] theorem mirabolicCompactInclusion_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) :
    mirabolicCompactInclusion ψ n f = f.val := rfl

/-- The canonical inclusion is injective. -/
theorem mirabolicCompactInclusion_injective (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Function.Injective (mirabolicCompactInclusion ψ n) :=
  Subtype.val_injective

/-- Evaluation of the compact model uses exactly its underlying function. -/
def mirabolicCompactEval (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) (g : mirabolic n F) : ℂ :=
  mirabolicEval ψ n f.val g

@[simp] theorem mirabolicCompactEval_def (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) (g : mirabolic n F) :
    mirabolicCompactEval ψ n f g = f.val.val.val g := rfl

@[simp] theorem mirabolicCompactInclusion_eval (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) (g : mirabolic n F) :
    mirabolicEval ψ n (mirabolicCompactInclusion ψ n f) g =
      mirabolicCompactEval ψ n f g := rfl

@[simp] theorem mirabolicCompactEval_translate (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) (s g : mirabolic n F) :
    mirabolicCompactEval ψ n (mirabolicCompactInduced ψ n s f) g =
      mirabolicCompactEval ψ n f (g * s) := rfl

theorem mirabolicCompactEval_covariance (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (f : MirabolicCompactFunctions ψ n) (u : Mirabolic.upperUnipotent n F)
    (g : mirabolic n F) :
    mirabolicCompactEval ψ n f (u.val * g) =
      (mirabolicCharacter ψ n u : ℂ) * mirabolicCompactEval ψ n f g :=
  mirabolicEval_covariance ψ n f.val u g

theorem mirabolicSmoothInduced_smooth (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    IsSmooth (mirabolicSmoothInduced ψ n) :=
  Induction.smoothInduced_smooth _ _

theorem mirabolicCompactInduced_smooth (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    IsSmooth (mirabolicCompactInduced ψ n) :=
  Induction.compactInduced_smooth _ _

end Langlands.Whittaker
