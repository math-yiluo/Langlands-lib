import Langlands.Algebra.IdempotentedRingRightLimitAction
import Langlands.Algebra.IdempotentedRingRightLimitUniformity
import Mathlib.Algebra.Ring.PUnit

/-!
# Orbit-map extension targets for original nondegenerate modules

Renard I.1.3, printed p.9/PDF15. All uniformity and topology arguments
are explicitly the constructed ones and the discrete vector uniformity.
These proposition definitions provide statement coverage only.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

/-- Every original vector orbit is uniformly continuous into discrete original vectors. -/
def IdempotentedRingOriginalOrbitUniform (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] : Prop :=
  ∀ m : M, @UniformContinuous A M (idempotentedRingUniformSpace A)
    (⊥ : UniformSpace M) (fun a => a • m)

/-- The actual extended orbit is uniformly continuous for the actual family uniformity. -/
def IdempotentedRingRightLimitOrbitUniform (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) : Prop :=
  ∀ m : M, @UniformContinuous (IdempotentedRingRightLimit A) M
    (IdempotentedRingRightLimit.uniformSpace A) (⊥ : UniformSpace M)
    (fun x => IdempotentedRingRightLimitAction.act hM x m)

/-- The actual extended orbit is the unique continuous extension of the original orbit. -/
def IdempotentedRingRightLimitOrbitContinuousExtension (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) : Prop :=
  ∀ m : M,
    @Continuous (IdempotentedRingRightLimit A) M
      (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
      (⊥ : UniformSpace M).toTopologicalSpace
      (fun x => IdempotentedRingRightLimitAction.act hM x m) ∧
    (∀ a : A,
      IdempotentedRingRightLimitAction.act hM (IdempotentedRingRightLimit.canonical a) m =
        a • m) ∧
    (∀ f : IdempotentedRingRightLimit A → M,
      @Continuous (IdempotentedRingRightLimit A) M
        (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
        (⊥ : UniformSpace M).toTopologicalSpace f →
      (∀ a : A, f (IdempotentedRingRightLimit.canonical a) = a • m) →
      f = (fun x => IdempotentedRingRightLimitAction.act hM x m))

/-- The closed orbit extension target at the source's original module scope. -/
def IdempotentedRingOrbitExtensionTheorem : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    IsIdempotented A → ∀ hM : IsNondegenerate A M,
      IdempotentedRingOriginalOrbitUniform A M ∧
      IdempotentedRingRightLimitOrbitUniform A M hM ∧
      IdempotentedRingRightLimitOrbitContinuousExtension A M hM

/-! Complete unapplied statement interfaces at independent ring/carrier universes. -/

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → Prop :=
  @IdempotentedRingOriginalOrbitUniform.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → Prop :=
  @IdempotentedRingRightLimitOrbitUniform.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    IsNondegenerate A M → Prop :=
  @IdempotentedRingRightLimitOrbitContinuousExtension.{uA, uM}

example : Prop :=
  @IdempotentedRingOrbitExtensionTheorem.{uA, uM}

example : IdempotentedRingOrbitExtensionTheorem.{uA, uM} =
    (∀ (A : Type uA) (M : Type uM)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A → ∀ hM : IsNondegenerate A M,
        IdempotentedRingOriginalOrbitUniform A M ∧
        IdempotentedRingRightLimitOrbitUniform A M hM ∧
        IdempotentedRingRightLimitOrbitContinuousExtension A M hM) := rfl

example : IdempotentedRingOrbitExtensionTheorem.{0, 1} =
    (∀ (A : Type) (M : Type 1)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A → ∀ hM : IsNondegenerate A M,
        IdempotentedRingOriginalOrbitUniform A M ∧
        IdempotentedRingRightLimitOrbitUniform A M hM ∧
        IdempotentedRingRightLimitOrbitContinuousExtension A M hM) := rfl

example : IdempotentedRingOrbitExtensionTheorem.{1, 0} =
    (∀ (A : Type 1) (M : Type)
      [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
      IsIdempotented A → ∀ hM : IsNondegenerate A M,
        IdempotentedRingOriginalOrbitUniform A M ∧
        IdempotentedRingRightLimitOrbitUniform A M hM ∧
        IdempotentedRingRightLimitOrbitContinuousExtension A M hM) := rfl

/-! The selected structures are the actual ones. The vector codomain is Mathlib's
discrete topology, and the scalar action is the given original action. -/

example (M : Type uM) :
    (⊥ : UniformSpace M).toTopologicalSpace = (⊥ : TopologicalSpace M) := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [inst : NonUnitalModule A M] (a : A) (m : M) :
    a • m = NonUnitalModule.toEndHom inst a m := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    IdempotentedRingOriginalOrbitUniform A M =
      (let := idempotentedRingUniformSpace A
       let : UniformSpace M := ⊥
       ∀ m : M, UniformContinuous fun a : A => a • m) := rfl

example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) :
    IdempotentedRingRightLimitOrbitUniform A M hM =
      (let := IdempotentedRingRightLimit.uniformSpace A
       let : UniformSpace M := ⊥
       ∀ m : M, UniformContinuous fun x : IdempotentedRingRightLimit A =>
         IdempotentedRingRightLimitAction.act hM x m) := rfl

/-- The continuity clause uses the topology of the same actual family uniformity. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M) (h : IdempotentedRingRightLimitOrbitUniform A M hM)
    (m : M) :
    @Continuous (IdempotentedRingRightLimit A) M
      (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
      (⊥ : TopologicalSpace M)
      (fun x => IdempotentedRingRightLimitAction.act hM x m) :=
  @UniformContinuous.continuous (IdempotentedRingRightLimit A) M
    (IdempotentedRingRightLimit.uniformSpace A) ⊥ _ (h m)

/-- The extension target says that the actual extended orbit is the unique witness. -/
example (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hM : IsNondegenerate A M)
    (h : IdempotentedRingRightLimitOrbitContinuousExtension A M hM) (m : M) :
    ∃! f : IdempotentedRingRightLimit A → M,
      @Continuous (IdempotentedRingRightLimit A) M
        (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
        (⊥ : TopologicalSpace M) f ∧
      ∀ a : A, f (IdempotentedRingRightLimit.canonical a) = a • m :=
  ⟨fun x => IdempotentedRingRightLimitAction.act hM x m, ⟨(h m).1, (h m).2.1⟩,
    fun f hf => (h m).2.2 f hf.1 hf.2⟩

/-! The master target specializes to the original data, including the zero ring
acting on a trivial carrier, where both hypotheses hold. -/

example (h : IdempotentedRingOrbitExtensionTheorem.{uA, uM})
    (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) (m : M) (a : A) :
    IdempotentedRingRightLimitAction.act hM (IdempotentedRingRightLimit.canonical a) m =
      a • m :=
  ((h A M hA hM).2.2 m).2.1 a

example (h : IdempotentedRingOrbitExtensionTheorem.{0, 0}) :
    letI : NonUnitalModule PUnit.{1} PUnit.{1} := NonUnitalModule.ofEndHom 0
    ∃ hM : IsNondegenerate PUnit.{1} PUnit.{1},
      IdempotentedRingRightLimitOrbitContinuousExtension PUnit.{1} PUnit.{1} hM := by
  let : NonUnitalModule PUnit.{1} PUnit.{1} := NonUnitalModule.ofEndHom 0
  have hA : IsIdempotented PUnit.{1} :=
    fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, fun _ _ => rfl⟩
  have hM : IsNondegenerate PUnit.{1} PUnit.{1} :=
    fun _ => ⟨⟨0, IsIdempotentElem.zero⟩, rfl⟩
  exact ⟨hM, (h PUnit.{1} PUnit.{1} hA hM).2.2⟩

end Langlands.Algebra
