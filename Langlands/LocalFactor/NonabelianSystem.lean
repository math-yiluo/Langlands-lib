import Langlands.LocalFactor.CommonClosure
import Langlands.LocalFactor.Abelian.Definitions

/-!
# Local-constant systems in one common algebraic closure

The four local-constant laws are predicates on actual functions on the continuous
exact virtual groups. Existence and uniqueness are propositions only.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An unvalidated unit-valued assignment on the actual harmonic and exact
virtual inputs over every finite intermediate field. -/
abbrev Assignment :=
  ∀ E : Extension F, AdditiveCharacter F E → HaarMeasure F E → Virtual.{uF, uV} F E → ℂˣ

/-- Additivity of the exact virtual argument, written multiplicatively. -/
def AdditiveRelation (ε : Assignment.{uF, uV} F) : Prop :=
  ∀ E ψ μ x y, ε E ψ μ (x + y) = ε E ψ μ x * ε E ψ μ y

/-- Positive real scaling as a complex unit. Positivity supplies nonvanishing. -/
def positiveScale (c : NNReal) (hc : 0 < c) : ℂˣ :=
  Units.mk0 (c : ℂ) (by exact_mod_cast (ne_of_gt hc))

/-- Deligne's measure law with the actual integer virtual dimension. -/
def HaarScalingRelation (ε : Assignment.{uF, uV} F) : Prop :=
  ∀ E ψ μ (c : NNReal) (hc : 0 < c) x,
    ε E ψ (scaleHaar F E μ c hc) x =
      positiveScale c hc ^ degree F E x * ε E ψ μ x

/-- Degree-zero induction for every nested finite extension and arbitrary Haar
measures on both fields, with the actual field-trace additive character. -/
def InductionRelation (ε : Assignment.{uF, uV} F) : Prop :=
  ∀ (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (μL : HaarMeasure F L)
    (x : DegreeZero.{uF, uV} F L),
    ε E ψ μ (induce F E L h x.val) =
      ε L (traceCharacter F E L h ψ) μL x.val

/-- Rank-one agreement with the constructed abelian expression. The right side
is complex-valued; this equality does not presume its nonvanishing. -/
def RankOneRelation (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F) : Prop :=
  ∀ E (χ : FieldCharacter F E) ψ μ,
    (ε E ψ μ (characterClass F e E χ) : ℂ) =
      (fieldData F E).abelianEpsilonExpression χ ψ μ

/-- The common-closure system property. Normalized coherent reciprocity is an
explicit part of the property, and no assignment satisfying it is selected. -/
def IsSystem (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F) : Prop :=
  NormalizedReciprocity F e ∧ AdditiveRelation F ε ∧ HaarScalingRelation F ε ∧
    InductionRelation F ε ∧ RankOneRelation F e ε

/-- Conditional existence over this base field and its specified common closure.
This is a proposition, not an existence theorem or a chosen system. -/
def Exists (e : ReciprocityFamily F) : Prop :=
  NormalizedReciprocity F e → ∃ ε : Assignment.{uF, uV} F, IsSystem F e ε

/-- Uniqueness among assignments satisfying the same common-closure property.
No comparison between different base fields or closures is asserted here. -/
def Unique (e : ReciprocityFamily F) : Prop :=
  ∀ ε₁ ε₂ : Assignment.{uF, uV} F,
    IsSystem F e ε₁ → IsSystem F e ε₂ → ε₁ = ε₂

variable {F}

/-- Intrinsic normalization forced by multiplicativity in a group. -/
theorem value_zero {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    ε E ψ μ 0 = 1 := by
  have h := hε E ψ μ 0 0
  simpa only [zero_add, left_eq_mul] using h

/-- A negative virtual representation has the inverse local-constant value. -/
theorem value_neg {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (x : Virtual.{uF, uV} F E) : ε E ψ μ (-x) = (ε E ψ μ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hε, neg_add_cancel, value_zero hε]

/-- The exact quotient gives the original short-exact-sequence law on genuine
continuous representations, without an equivariant splitting hypothesis. -/
theorem value_shortExact {ε : Assignment.{uF, uV} F} (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    {A B C : {A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E) //
      A.IsContinuous}}
    {f : A.val.representation.IntertwiningMap B.val.representation}
    {g : B.val.representation.IntertwiningMap C.val.representation}
    (h : FiniteRepresentation.IsShortExact f g) :
    ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) B) =
      ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) A) *
        ε E ψ μ (ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) C) := by
  rw [ExactGrothendieckGroup.ofRepresentation_shortExact _ h, hε]

/-- A supplied system entails nonvanishing of the actual abelian expression;
no nonvanishing theorem is assumed to define that expression. -/
theorem abelianExpression_ne_zero {e : ReciprocityFamily F}
    {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε)
    (E : Extension F) (χ : FieldCharacter F E)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    (fieldData F E).abelianEpsilonExpression χ ψ μ ≠ 0 := by
  rw [← hε.2.2.2.2 E χ ψ μ]
  exact Units.ne_zero _

end Langlands.LocalFactor.NonabelianSystem
