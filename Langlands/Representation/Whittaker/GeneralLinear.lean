import Langlands.Group.GL.UpperUnipotent
import Langlands.HarmonicAnalysis.Basic
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Whittaker.Algebraic

/-!
# Standard Whittaker characters and coefficient models on actual GL

Positive rank is written `n + 1`, so rank one is included without a separate
placeholder group. The module topology is never used.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F]

/-- The standard character on the actual upper-unipotent matrix subgroup. -/
def standardCharacter (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    upperUnipotent (n + 1) F →* ℂˣ :=
  Circle.toUnits.comp
    (ψ.toAddChar.toMonoidHom.comp UpperUnipotent.superdiagonalSum)

/-- Its complex value is the additive character of the first-superdiagonal sum. -/
@[simp] theorem standardCharacter_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : upperUnipotent (n + 1) F) :
    (standardCharacter ψ n g : ℂ) =
      ψ.complex (∑ i : Fin n, g.val i.castSucc i.succ) := rfl

/-- The standard character is unitary. -/
@[simp] theorem norm_standardCharacter (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : upperUnipotent (n + 1) F) :
    ‖(standardCharacter ψ n g : ℂ)‖ = 1 := by
  rw [standardCharacter_apply, ψ.norm_complex]

/-- Rank one has the trivial unipotent character, since the sum is empty. -/
@[simp] theorem standardCharacter_rankOne (ψ : UnitaryAdditiveCharacter F) :
    standardCharacter ψ 0 = 1 := by
  ext g
  simp [standardCharacter_apply]

/-- The character for the second member of a JPSS pair is the pointwise inverse. -/
def inverseStandardCharacter (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    upperUnipotent (n + 1) F →* ℂˣ :=
  (standardCharacter ψ n)⁻¹

@[simp] theorem inverseStandardCharacter_apply (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (g : upperUnipotent (n + 1) F) :
    (inverseStandardCharacter ψ n g : ℂ) =
      (ψ.complex (∑ i : Fin n, g.val i.castSucc i.succ))⁻¹ := by
  rfl

/-- The change-of-additive-character interface `ψ(x) ↦ ψ(a*x)` on unipotent matrices.
It constructs a group character, without duplicating the shared additive-character type. -/
def scaledStandardCharacter (ψ : UnitaryAdditiveCharacter F) (a : Fˣ) (n : ℕ) :
    upperUnipotent (n + 1) F →* ℂˣ :=
  Circle.toUnits.comp
    (ψ.toAddChar.toMonoidHom.comp
      ((AddMonoidHom.mulLeft (a : F)).toMultiplicative.comp
        UpperUnipotent.superdiagonalSum))

@[simp] theorem scaledStandardCharacter_apply (ψ : UnitaryAdditiveCharacter F)
    (a : Fˣ) (n : ℕ) (g : upperUnipotent (n + 1) F) :
    (scaledStandardCharacter ψ a n g : ℂ) =
      ψ.complex ((a : F) * ∑ i : Fin n, g.val i.castSucc i.succ) := rfl

@[simp] theorem scaledStandardCharacter_one (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    scaledStandardCharacter ψ 1 n = standardCharacter ψ n := by
  ext g
  simp

/-- Scaling the additive argument by `-1` gives the inverse character. -/
@[simp] theorem scaledStandardCharacter_neg_one (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    scaledStandardCharacter ψ (-1) n = inverseStandardCharacter ψ n := by
  ext g
  simp [scaledStandardCharacter_apply, inverseStandardCharacter_apply,
    AddChar.map_neg_eq_inv]

section CharacterTopology

variable [IsTopologicalRing F]

/-- Continuity of the actual matrix character, with the usual topology on complex units. -/
def standardCharacterContinuous (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    ContinuousMonoidHom (upperUnipotent (n + 1) F) ℂˣ where
  toMonoidHom := standardCharacter ψ n
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have h : Continuous (fun g : upperUnipotent (n + 1) F =>
        ψ (∑ i : Fin n, g.val i.castSucc i.succ)) :=
      ψ.continuous_toFun.comp
        (continuous_toAdd.comp UpperUnipotent.superdiagonalSumContinuous.continuous)
    exact ⟨continuous_subtype_val.comp h, continuous_subtype_val.comp h.inv⟩

/-- The inverse character retains continuity. -/
def inverseStandardCharacterContinuous (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    ContinuousMonoidHom (upperUnipotent (n + 1) F) ℂˣ where
  toMonoidHom := inverseStandardCharacter ψ n
  continuous_toFun := (standardCharacterContinuous ψ n).continuous.inv

/-- Continuity also holds for every scaled additive argument. -/
def scaledStandardCharacterContinuous (ψ : UnitaryAdditiveCharacter F)
    (a : Fˣ) (n : ℕ) :
    ContinuousMonoidHom (upperUnipotent (n + 1) F) ℂˣ where
  toMonoidHom := scaledStandardCharacter ψ a n
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have hs : Continuous (fun g : upperUnipotent (n + 1) F =>
        ∑ i : Fin n, g.val i.castSucc i.succ) :=
      continuous_toAdd.comp UpperUnipotent.superdiagonalSumContinuous.continuous
    have h : Continuous (fun g : upperUnipotent (n + 1) F =>
        ψ ((a : F) * ∑ i : Fin n, g.val i.castSucc i.succ)) :=
      ψ.continuous_toFun.comp (continuous_const.mul hs)
    exact ⟨continuous_subtype_val.comp h, continuous_subtype_val.comp h.inv⟩

end CharacterTopology

section Models

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The actual space of standard Whittaker functionals on `π`. -/
abbrev glFunctionals : Submodule ℂ (Module.Dual ℂ V) :=
  functionals (upperUnipotent (n + 1) F) (standardCharacter ψ n) π

/-- Functionals using the inverse character, as required for the second member of a pair. -/
abbrev glInverseFunctionals : Submodule ℂ (Module.Dual ℂ V) :=
  functionals (upperUnipotent (n + 1) F) (inverseStandardCharacter ψ n) π

/-- The standard coefficient-image model for a specified Whittaker functional. -/
abbrev glCoefficientModel (ℓ : glFunctionals ψ n π) :=
  coefficientModel π ℓ

/-- The right-translation representation carried by that actual image. -/
abbrev glModelRepresentation (ℓ : glFunctionals ψ n π) :=
  modelRepresentation π ℓ

/-- A model vector is an actual complex-valued function on `GL_(n+1)`. -/
def glModelFunction (ℓ : glFunctionals ψ n π)
    (w : (glCoefficientModel ψ n π ℓ).toSubmodule) :
    Langlands.GeneralLinear (n + 1) F → ℂ :=
  w.val.val

theorem glModelFunction_equivariance (ℓ : glFunctionals ψ n π)
    (w : (glCoefficientModel ψ n π ℓ).toSubmodule)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    glModelFunction ψ n π ℓ w (u.val * g) =
      (standardCharacter ψ n u : ℂ) * glModelFunction ψ n π ℓ w g :=
  w.val.property u g

theorem glModelFunction_translate (ℓ : glFunctionals ψ n π)
    (w : (glCoefficientModel ψ n π ℓ).toSubmodule)
    (s g : Langlands.GeneralLinear (n + 1) F) :
    glModelFunction ψ n π ℓ (glModelRepresentation ψ n π ℓ s w) g =
      glModelFunction ψ n π ℓ w (g * s) := rfl

/-- Genericity here includes irreducibility and admissibility, and requires an
actual nonzero standard Whittaker functional. No multiplicity-one theorem is assumed. -/
def IsGeneric : Prop :=
  Representation.IsIrreducible π ∧ IsAdmissible π ∧
    HasFunctional (N := upperUnipotent (n + 1) F) (θ := standardCharacter ψ n) π

/-- A specified nonzero functional realizes an irreducible representation in its model. -/
noncomputable abbrev glModelEquiv [Representation.IsIrreducible π]
    (ℓ : glFunctionals ψ n π) (hℓ : ℓ.val ≠ 0) :
    π.Equiv (glModelRepresentation ψ n π ℓ) :=
  modelEquiv π ℓ hℓ

/-- Smoothness of the coefficient model follows from smoothness of the original action. -/
theorem glModel_isSmooth (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π) :
    IsSmooth (V := (glCoefficientModel ψ n π ℓ).toSubmodule)
      (glModelRepresentation ψ n π ℓ) :=
  model_isSmooth π hπ ℓ

end Models

/-- In rank one, every algebraic linear form satisfies the unipotent condition. -/
theorem glFunctionals_rankOne {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (Langlands.GeneralLinear 1 F) V) :
    glFunctionals ψ 0 π = ⊤ := by
  apply top_unique
  intro ℓ _ u v
  have hu : u.val = 1 := by
    apply Units.ext
    ext i j
    have hij : i = j := Fin.ext (by omega)
    subst j
    simp
  change ℓ (π u.val v) = (standardCharacter ψ 0 u : ℂ) * ℓ v
  rw [hu, map_one, Module.End.one_apply, standardCharacter_rankOne]
  simp

section ModelRegularity

variable [IsTopologicalRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Every vector in the model of a smooth representation is a locally constant function. -/
theorem glModelFunction_isLocallyConstant (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ n π) (w : (glCoefficientModel ψ n π ℓ).toSubmodule) :
    IsLocallyConstant (glModelFunction ψ n π ℓ w) := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ w
  exact Langlands.matrixCoefficient_isLocallyConstant π ℓ.val v (hπ v)

/-- Consequently the model functions are continuous, for the usual complex topology. -/
theorem glModelFunction_continuous (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ n π) (w : (glCoefficientModel ψ n π ℓ).toSubmodule) :
    Continuous (glModelFunction ψ n π ℓ w) :=
  (glModelFunction_isLocallyConstant ψ n π hπ ℓ w).continuous

end ModelRegularity

end Langlands.Whittaker
