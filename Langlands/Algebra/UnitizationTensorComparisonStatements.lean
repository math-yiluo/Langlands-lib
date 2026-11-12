import Langlands.Algebra.CompatibleUnitizationTensor
import Langlands.Algebra.NondegenerateTensorScalars
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Renard I.2.1: the unitized tensor comparison and the algebra structure on the unitization

Renard (9 July 2026), I.2.1 on printed p. 14 / PDF20. Proposition definitions for the three
assertions of that section that had no published statement: the kernel of the comparison
`X ⊗_A Y → X ⊗_Ã Y`, the tensor half of (I.2.1.2) for nondegenerate modules with their canonical
scalars (with its unital special case), and the uniqueness of the algebra structure on
`Ã = A ⊕ k·1`. All objects are the published ones of `CompatibleUnitizationTensor`,
`NondegenerateScalars` and `NondegenerateTensorScalars`, and Mathlib's `Unitization`.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationTensorComparison

open MulOpposite

attribute [local instance] NondegenerateTensorScalars.opIsScalarTower
  NondegenerateTensorScalars.opSMulCommClass

universe uK uA uX uY

/-- Renard I.2.1, `X ⊗_Ã Y = X ⊗_A Y / Vect({λx ⊗ y − x ⊗ λy})`. For compatible `k`-module
structures on a right module `X` and a left module `Y`, the kernel of the comparison
`q : X ⊗_A Y →+ X ⊗_Ã Y` is exactly the published integer span `H` of the scalar-balancing
differences, and the descended comparison `X ⊗_A Y ⧸ H →+ X ⊗_Ã Y` is bijective. -/
def ScalarQuotientComparisonStatement : Prop :=
  ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [Module k X] [NonUnitalModule Aᵐᵒᵖ X]
    [IsScalarTower k Aᵐᵒᵖ X] [SMulCommClass k Aᵐᵒᵖ X]
    [AddCommGroup Y] [Module k Y] [NonUnitalModule A Y]
    [IsScalarTower k A Y] [SMulCommClass k A Y],
    LinearMap.ker (CompatibleUnitizationTensor.comparison k A X Y).toIntLinearMap =
        CompatibleUnitizationTensor.scalarRelations k A X Y ∧
      Function.Bijective (CompatibleUnitizationTensor.descendedComparison k A X Y)

/-- Renard (I.2.1.2), tensor half: for an idempotented algebra `A`, a nondegenerate right module
`X` and a nondegenerate left module `Y`, each with its published canonical scalars, the
comparison `q : X ⊗_A Y →+ X ⊗_Ã Y` is bijective. -/
def NondegenerateUnitizedTensorStatement : Prop :=
  ∀ (k : Type uK) (A : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A]
    [AddCommGroup X] [NonUnitalModule Aᵐᵒᵖ X] [AddCommGroup Y] [NonUnitalModule A Y]
    (hA : IsIdempotented A) (hX : IsNondegenerate Aᵐᵒᵖ X) (hY : IsNondegenerate A Y),
    letI := NondegenerateTensorScalars.rightModule k hA hX
    letI := NondegenerateTensorScalars.leftModule k hA hY
    haveI := NondegenerateScalars.isScalarTower k hA.op hX
    haveI := NondegenerateScalars.smulCommClass k hA.op hX
    haveI := NondegenerateScalars.isScalarTower k hA hY
    haveI := NondegenerateScalars.smulCommClass k hA hY
    Function.Bijective (CompatibleUnitizationTensor.comparison k A X Y)

/-- Renard I.2.1, "en particulier" after (I.2.1.2), tensor half: for a unital algebra `R`, a
unital right module `X` and a unital left module `Y`, each with its published unital canonical
scalars `c • m = (c • 1) • m`, the comparison `q : X ⊗_R Y →+ X ⊗_R̃ Y` is bijective. -/
def UnitalUnitizedTensorStatement : Prop :=
  ∀ (k : Type uK) (R : Type uA) (X : Type uX) (Y : Type uY)
    [CommRing k] [Ring R] [Algebra k R]
    [AddCommGroup X] [NonUnitalModule Rᵐᵒᵖ X] [AddCommGroup Y] [NonUnitalModule R Y]
    (hX : IsUnitalModule Rᵐᵒᵖ X) (hY : IsUnitalModule R Y),
    letI := NondegenerateScalars.unitalModule k hX
    letI := NondegenerateScalars.unitalModule k hY
    haveI := NondegenerateScalars.isScalarTower k (IsIdempotented.of_ring Rᵐᵒᵖ)
      (isNondegenerate_iff_isUnitalModule.mpr hX)
    haveI := NondegenerateScalars.smulCommClass k (IsIdempotented.of_ring Rᵐᵒᵖ)
      (isNondegenerate_iff_isUnitalModule.mpr hX)
    haveI := NondegenerateScalars.isScalarTower k (IsIdempotented.of_ring R)
      (isNondegenerate_iff_isUnitalModule.mpr hY)
    haveI := NondegenerateScalars.smulCommClass k (IsIdempotented.of_ring R)
      (isNondegenerate_iff_isUnitalModule.mpr hY)
    Function.Bijective (CompatibleUnitizationTensor.comparison k R X Y)

/-- Renard I.2.1, `Ã = A ⊕ k·1_A` with `1_A` declared to be the unit "détermine une unique
structure d'algèbre sur `Ã`". The multiplication of Mathlib's `Unitization k A` is associative,
has `1` as a two-sided unit and extends the multiplication of `A`; and every `k`-bilinear
multiplication on `Unitization k A` with `1` as a two-sided unit that extends the multiplication
of `A` is this one. -/
def UnitizationAlgebraUniqueStatement : Prop :=
  ∀ (k : Type uK) (A : Type uA)
    [CommRing k] [NonUnitalRing A] [Module k A] [IsScalarTower k A A] [SMulCommClass k A A],
    ((∀ u v w : Unitization k A, u * v * w = u * (v * w)) ∧
      (∀ u : Unitization k A, 1 * u = u ∧ u * 1 = u) ∧
      (∀ a b : A, ((a : Unitization k A) * (b : Unitization k A)) = ((a * b : A) : Unitization k A))) ∧
    ∀ μ : Unitization k A →ₗ[k] Unitization k A →ₗ[k] Unitization k A,
      (∀ u : Unitization k A, μ 1 u = u) →
      (∀ u : Unitization k A, μ u 1 = u) →
      (∀ a b : A, μ (a : Unitization k A) (b : Unitization k A) = ((a * b : A) : Unitization k A)) →
      μ = LinearMap.mul k (Unitization k A)

/-- The four I.2.1 assertions together. -/
def Statements : Prop :=
  ScalarQuotientComparisonStatement.{uK, uA, uX, uY} ∧
    NondegenerateUnitizedTensorStatement.{uK, uA, uX, uY} ∧
    UnitalUnitizedTensorStatement.{uK, uA, uX, uY} ∧
    UnitizationAlgebraUniqueStatement.{uK, uA}

end Langlands.Algebra.UnitizationTensorComparison
