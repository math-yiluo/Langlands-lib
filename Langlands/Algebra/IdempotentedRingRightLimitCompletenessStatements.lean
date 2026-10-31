import Langlands.Algebra.IdempotentedRingRightLimitUniformity
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Ring.PUnit

/-!
# Closedness, density and completeness targets for the actual right-image inverse limit

Renard I.1.3, printed p.9/PDF15 proves density and leaves completeness to
the reader. Closedness in the full discrete product is an internal target.
These proposition definitions provide statement coverage only.
-/

set_option autoImplicit false

namespace Langlands.Algebra

universe uA

/-- The actual compatible families form a closed subset of the full product of
discrete original carriers. -/
def IdempotentedRingRightLimitClosedFamily (A : Type uA) [NonUnitalRing A] : Prop :=
  @IsClosed (Idempotent A → A)
    (IdempotentedRingRightLimit.discreteProductUniformSpace A).toTopologicalSpace
    (rightCompatibleFamilies A : Set (Idempotent A → A))

/-- The actual coordinate uniformity on the existing family carrier is complete. -/
def IdempotentedRingRightLimitComplete (A : Type uA) [NonUnitalRing A] : Prop :=
  @CompleteSpace (IdempotentedRingRightLimit A) (IdempotentedRingRightLimit.uniformSpace A)

/-- The original canonical additive map has dense range in the actual family topology. -/
def IdempotentedRingRightLimitCanonicalDense (A : Type uA) [NonUnitalRing A] : Prop :=
  @DenseRange (IdempotentedRingRightLimit A)
    (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace A
    (IdempotentedRingRightLimit.canonical (A := A))

/-- The same canonical map is a dense embedding for the two exact uniform topologies. -/
def IdempotentedRingRightLimitCanonicalDenseEmbedding
    (A : Type uA) [NonUnitalRing A] : Prop :=
  @IsDenseEmbedding A (IdempotentedRingRightLimit A)
    (idempotentedRingUniformSpace A).toTopologicalSpace
    (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
    (IdempotentedRingRightLimit.canonical (A := A))

/-- Closed target: closedness and completeness for every nonunital ring; density and
dense embedding under the original finite-local-unit condition. -/
def IdempotentedRingRightLimitDensityCompletenessTheorem : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    IdempotentedRingRightLimitClosedFamily A ∧
    IdempotentedRingRightLimitComplete A ∧
    (IsIdempotented A →
      IdempotentedRingRightLimitCanonicalDense A ∧
      IdempotentedRingRightLimitCanonicalDenseEmbedding A)

/-! Complete unapplied interfaces at an arbitrary original-ring universe. -/

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightLimitClosedFamily.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightLimitComplete.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightLimitCanonicalDense.{uA}

example : (A : Type uA) → [NonUnitalRing A] → Prop :=
  @IdempotentedRingRightLimitCanonicalDenseEmbedding.{uA}

example : Prop :=
  @IdempotentedRingRightLimitDensityCompletenessTheorem.{uA}

/-! The selected topologies are the actual constructed ones. The full product
topology is Mathlib's product of discrete topologies on the original carrier,
and the codomain topology agrees with the locally installed actual uniformity. -/

example (A : Type uA) [NonUnitalRing A] :
    (IdempotentedRingRightLimit.discreteProductUniformSpace A).toTopologicalSpace =
      @Pi.topologicalSpace (Idempotent A) (fun _ => A) (fun _ => ⊥) := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitClosedFamily A =
      (let := IdempotentedRingRightLimit.discreteProductUniformSpace A
       IsClosed {a : Idempotent A → A | (∀ e, a e * (e : A) = a e) ∧
         ∀ e f, e ≤ f → a f * (e : A) = a e}) := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitComplete A =
      (let := IdempotentedRingRightLimit.uniformSpace A
       CompleteSpace (IdempotentedRingRightLimit A)) := rfl

example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitCanonicalDense A =
      (let := IdempotentedRingRightLimit.uniformSpace A
       Dense (Set.range fun a : A => IdempotentedRingRightLimit.canonical a)) := rfl

/-- The dense-embedding target selects the same codomain topology as the density target. -/
example (A : Type uA) [NonUnitalRing A]
    (h : IdempotentedRingRightLimitCanonicalDenseEmbedding A) :
    IdempotentedRingRightLimitCanonicalDense A :=
  @IsDenseInducing.dense A (IdempotentedRingRightLimit A)
    (idempotentedRingUniformSpace A).toTopologicalSpace
    (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace _
    (@IsDenseEmbedding.toIsDenseInducing A (IdempotentedRingRightLimit A)
      (idempotentedRingUniformSpace A).toTopologicalSpace
      (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace _ h)

/-- The dense-embedding target is inducing for the original topology and injective. -/
example (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitCanonicalDenseEmbedding A →
      @Topology.IsInducing A (IdempotentedRingRightLimit A)
        (idempotentedRingUniformSpace A).toTopologicalSpace
        (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
        (IdempotentedRingRightLimit.canonical (A := A)) ∧
      Function.Injective (IdempotentedRingRightLimit.canonical (A := A)) :=
  fun h =>
    ⟨@IsDenseInducing.toIsInducing A (IdempotentedRingRightLimit A)
        (idempotentedRingUniformSpace A).toTopologicalSpace
        (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace _
        (@IsDenseEmbedding.toIsDenseInducing A (IdempotentedRingRightLimit A)
          (idempotentedRingUniformSpace A).toTopologicalSpace
          (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace _ h),
      @IsDenseEmbedding.injective A (IdempotentedRingRightLimit A)
        (idempotentedRingUniformSpace A).toTopologicalSpace
        (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace _ h⟩

/-! The master target specializes to every original ring, including zero rings. -/

example (h : IdempotentedRingRightLimitDensityCompletenessTheorem.{uA})
    (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    IdempotentedRingRightLimitCanonicalDenseEmbedding A :=
  ((h A).2.2 hA).2

example (h : IdempotentedRingRightLimitDensityCompletenessTheorem.{0}) :
    IdempotentedRingRightLimitComplete PUnit.{1} :=
  (h PUnit.{1}).2.1

end Langlands.Algebra
