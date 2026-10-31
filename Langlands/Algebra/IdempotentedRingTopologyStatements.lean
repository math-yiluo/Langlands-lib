import Langlands.Algebra.IdempotentedRingUniformity
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.UniformSpace.Separation

/-!
# Laws of the actual right-coordinate topology

Exact targets for intrinsic consequences of Renard I.1.3.
These proposition definitions provide statement coverage only.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA

/-- Compatibility of the actual coordinate uniformity with the original additive group. -/
def IdempotentedRingUniformAddGroup (A : Type uA) [NonUnitalRing A] : Prop :=
  let := idempotentedRingUniformSpace A
  IsUniformAddGroup A

/-- Equality of all actual right coordinates detects equality in the original ring. -/
def IdempotentedRingRightCoordinatesSeparate (A : Type uA) [NonUnitalRing A] : Prop :=
  ∀ a b : A, (∀ e : Idempotent A, a * (e : A) = b * (e : A)) ↔ a = b

/-- The topology induced by the actual coordinate uniformity is Hausdorff. -/
def IdempotentedRingHausdorff (A : Type uA) [NonUnitalRing A] : Prop :=
  let := idempotentedRingUniformSpace A
  T2Space A

/-- Every actual left multiplication is uniformly continuous for the actual uniformity. -/
def IdempotentedRingLeftMultiplicationUniform (A : Type uA) [NonUnitalRing A] : Prop :=
  let := idempotentedRingUniformSpace A
  ∀ b : A, UniformContinuous (fun a : A => b * a)

/-- Every actual right multiplication is uniformly continuous for the actual uniformity. -/
def IdempotentedRingRightMultiplicationUniform (A : Type uA) [NonUnitalRing A] : Prop :=
  let := idempotentedRingUniformSpace A
  ∀ b : A, UniformContinuous (fun a : A => a * b)

/-- Original addition, negation and joint multiplication are continuous. -/
def IdempotentedRingTopologicalRing (A : Type uA) [NonUnitalRing A] : Prop :=
  let := idempotentedRingUniformSpace A
  IsTopologicalRing A

/-- Closed target, retaining weaker hypotheses for the additive and left-multiplication laws. -/
def IdempotentedRingTopologyTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    IdempotentedRingUniformAddGroup A ∧
    IdempotentedRingLeftMultiplicationUniform A ∧
    (IsIdempotented A →
      IdempotentedRingRightCoordinatesSeparate A ∧
      IdempotentedRingHausdorff A ∧
      IdempotentedRingRightMultiplicationUniform A ∧
      IdempotentedRingTopologicalRing A)

/-! Complete unapplied interfaces, together with the actual local-structure formulas. -/

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingUniformAddGroup.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightCoordinatesSeparate.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingHausdorff.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingLeftMultiplicationUniform.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightMultiplicationUniform.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingTopologicalRing.{uA}

example : Prop :=
  IdempotentedRingTopologyTheorem.{uA}

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingLeftMultiplicationUniform A =
      ∀ b : A, @UniformContinuous A A (idempotentedRingUniformSpace A)
        (idempotentedRingUniformSpace A) (fun a : A => b * a) := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightMultiplicationUniform A =
      ∀ b : A, @UniformContinuous A A (idempotentedRingUniformSpace A)
        (idempotentedRingUniformSpace A) (fun a : A => a * b) := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingUniformAddGroup A =
      @IsUniformAddGroup A (idempotentedRingUniformSpace A) _ := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingHausdorff A =
      @T2Space A (idempotentedRingUniformSpace A).toTopologicalSpace := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingTopologicalRing A =
      @IsTopologicalRing A (idempotentedRingUniformSpace A).toTopologicalSpace _ := rfl

end Langlands.Algebra
