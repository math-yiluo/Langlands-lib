import Langlands.Algebra.IdempotentedRingEndomorphism
import Langlands.Algebra.IdempotentedRingRightLimitUniformity
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.PUnit
import Mathlib.Topology.UniformSpace.Equiv

/-!
# Comparison and closure targets for the actual right-linear endomorphism model

Renard I.1.4, printed p.10/PDF16, and I.1.6, printed pp.11-12/PDF17-18.
These proposition definitions provide statement coverage only.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open IdempotentedRingEndomorphism

universe uA

/-- Both inverse identities for the fixed forward ring map and the fixed reverse
idempotent evaluation. -/
def IdempotentedRingEndomorphismInverseIdentities : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    (∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
      ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β

/-- An actual unital ring equivalence, for the published family ring, whose entire
forward and inverse functions are the fixed maps. -/
def IdempotentedRingEndomorphismRingEquivalence : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    letI := IdempotentedRingRightLimit.ring hA
    ∃ Φ : IdempotentedRingRightLimit A ≃+* RightLinearEnd A,
      (Φ : IdempotentedRingRightLimit A → RightLinearEnd A) =
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A) ∧
        (Φ.symm : RightLinearEnd A → IdempotentedRingRightLimit A) =
          (idempotentEvaluation : RightLinearEnd A → IdempotentedRingRightLimit A)

/-- The restricted pointwise uniformity pulls back along the actual forward map to
exactly the discrete-coordinate family uniformity. -/
def IdempotentedRingEndomorphismUniformityComparison : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
    UniformSpace.comap
        (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
        (rightLinearEndUniformSpace A) =
      IdempotentedRingRightLimit.uniformSpace A

/-- The actual right-linear subset is closed among all additive endomorphisms for
the specified pointwise topology. -/
def IdempotentedRingEndomorphismRightLinearClosed : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
      (rightLinearEnd A : Set (AddMonoid.End A))

/-- Renard's I.1.6 lemma: the pointwise closure of the actual left multiplications
in all additive endomorphisms is the actual right-linear subset. -/
def IdempotentedRingEndomorphismClosureLemma : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
    @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
      (rightLinearEnd A : Set (AddMonoid.End A))

/-- Aggregate target: the five component statements at the same arbitrary universe. -/
def IdempotentedRingEndomorphismComparisonTheorem : Prop :=
  IdempotentedRingEndomorphismInverseIdentities.{uA} ∧
    IdempotentedRingEndomorphismRingEquivalence.{uA} ∧
    IdempotentedRingEndomorphismUniformityComparison.{uA} ∧
    IdempotentedRingEndomorphismRightLinearClosed.{uA} ∧
    IdempotentedRingEndomorphismClosureLemma.{uA}

/-! Complete unapplied interfaces at an arbitrary universe and at universes 0 and 1. -/

section Interfaces

example : Prop := @IdempotentedRingEndomorphismInverseIdentities.{uA}
example : Prop := @IdempotentedRingEndomorphismRingEquivalence.{uA}
example : Prop := @IdempotentedRingEndomorphismUniformityComparison.{uA}
example : Prop := @IdempotentedRingEndomorphismRightLinearClosed.{uA}
example : Prop := @IdempotentedRingEndomorphismClosureLemma.{uA}
example : Prop := @IdempotentedRingEndomorphismComparisonTheorem.{uA}

example : Prop := @IdempotentedRingEndomorphismInverseIdentities.{0}
example : Prop := @IdempotentedRingEndomorphismRingEquivalence.{0}
example : Prop := @IdempotentedRingEndomorphismUniformityComparison.{0}
example : Prop := @IdempotentedRingEndomorphismRightLinearClosed.{0}
example : Prop := @IdempotentedRingEndomorphismClosureLemma.{0}
example : Prop := @IdempotentedRingEndomorphismComparisonTheorem.{0}

example : Prop := @IdempotentedRingEndomorphismInverseIdentities.{1}
example : Prop := @IdempotentedRingEndomorphismRingEquivalence.{1}
example : Prop := @IdempotentedRingEndomorphismUniformityComparison.{1}
example : Prop := @IdempotentedRingEndomorphismRightLinearClosed.{1}
example : Prop := @IdempotentedRingEndomorphismClosureLemma.{1}
example : Prop := @IdempotentedRingEndomorphismComparisonTheorem.{1}

end Interfaces

/-! Explicit unfoldings: every ring, uniformity and topology is the named construction,
and the right-linear membership is the original equation. -/

section Unfoldings

/-- The ring equivalence uses the multiplication and addition of exactly
`IdempotentedRingRightLimit.ring hA` on the published family carrier. -/
example : IdempotentedRingEndomorphismRingEquivalence.{uA} =
    ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      ∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
          (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _,
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
          ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
            ⇑(idempotentEvaluation (A := A)) := rfl

/-- The installed family multiplication and identity are the published ones. -/
example (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    letI := IdempotentedRingRightLimit.ring hA
    (∀ x y : IdempotentedRingRightLimit A,
        x * y = IdempotentedRingRightLimit.product hA x y) ∧
      (1 : IdempotentedRingRightLimit A) = IdempotentedRingRightLimit.unit :=
  ⟨fun _ _ => rfl, rfl⟩

/-- Multiplication in the right-linear subring is actual composition, with the left
factor applied after the right factor. -/
example (A : Type uA) [NonUnitalRing A] (β γ : RightLinearEnd A) (a : A) :
    (β * γ).val a = β.val (γ.val a) := rfl

/-- The comparison uses exactly the restriction of the pointwise uniformity. -/
example : IdempotentedRingEndomorphismUniformityComparison.{uA} =
    ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      UniformSpace.comap (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (UniformSpace.comap (fun β : RightLinearEnd A => β.val)
            (UniformSpace.comap (fun β : AddMonoid.End A => (β : A → A))
              (@Pi.uniformSpace A (fun _ : A => A)
                (fun _ => idempotentedRingUniformSpace A)))) =
        ⨅ e : Idempotent A,
          UniformSpace.comap (fun x : IdempotentedRingRightLimit A => x.val e)
            (⊥ : UniformSpace A) := rfl

/-- Equivalently, the actual evaluation map `x ↦ (a ↦ applyOriginal hA x a)` pulls
the product of the original value uniformities back to the family uniformity. -/
example : IdempotentedRingEndomorphismUniformityComparison.{uA} ↔
    ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
          (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) =
        IdempotentedRingRightLimit.uniformSpace A := by
  have key : ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      UniformSpace.comap
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (rightLinearEndUniformSpace A) =
        UniformSpace.comap (IdempotentedRingRightLimit.applyOriginal hA)
          (@Pi.uniformSpace A (fun _ : A => A) (fun _ => idempotentedRingUniformSpace A)) := by
    intro A _ hA
    rw [rightLinearEndUniformSpace_eq_function_comap, ← UniformSpace.comap_comap]
    rfl
  constructor
  · intro h A _ hA
    rw [← key A hA]
    exact h A hA
  · intro h A _ hA
    rw [key A hA]
    exact h A hA

/-- The closedness target is closedness of exactly the original right-linear equation,
for the topology induced from the product of the original value topologies. -/
example : IdempotentedRingEndomorphismRightLinearClosed.{uA} =
    ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
      @IsClosed (AddMonoid.End A)
        (TopologicalSpace.induced (fun β : AddMonoid.End A => (β : A → A))
          (@Pi.topologicalSpace A (fun _ : A => A)
            (fun _ => (idempotentedRingUniformSpace A).toTopologicalSpace)))
        {β : AddMonoid.End A | ∀ a b : A, β (a * b) = β a * b} := rfl

/-- The closure target takes the closure of exactly the range of `b ↦ a*b`, in all
additive endomorphisms, for the same topology. -/
example : IdempotentedRingEndomorphismClosureLemma.{uA} =
    ∀ (A : Type uA) [NonUnitalRing A], IsIdempotented A →
      @closure (AddMonoid.End A)
          (TopologicalSpace.induced (fun β : AddMonoid.End A => (β : A → A))
            (@Pi.topologicalSpace A (fun _ : A => A)
              (fun _ => (idempotentedRingUniformSpace A).toTopologicalSpace)))
          (Set.range (AddMonoidHom.mulLeft : A → AddMonoid.End A)) =
        {β : AddMonoid.End A | ∀ a b : A, β (a * b) = β a * b} := rfl

/-- The inverse identities are equivalently identities of the complete composites. -/
example : IdempotentedRingEndomorphismInverseIdentities.{uA} ↔
    ∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A),
      (idempotentEvaluation : RightLinearEnd A → IdempotentedRingRightLimit A) ∘
            (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A) = id ∧
        (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A) ∘
            (idempotentEvaluation : RightLinearEnd A → IdempotentedRingRightLimit A) = id :=
  ⟨fun h A _ hA => ⟨funext (h A hA).1, funext (h A hA).2⟩,
    fun h A _ hA => ⟨fun x => congrFun (h A hA).1 x, fun β => congrFun (h A hA).2 β⟩⟩

end Unfoldings

/-! Consistency between the components. These are not proofs of any target. -/

section Consistency

/-- The specified ring equivalence exists exactly when both inverse identities hold. -/
example : IdempotentedRingEndomorphismInverseIdentities.{uA} ↔
    IdempotentedRingEndomorphismRingEquivalence.{uA} := by
  constructor
  · intro h A _ hA
    let := IdempotentedRingRightLimit.ring hA
    obtain ⟨hl, hr⟩ := h A hA
    exact ⟨{ toFun := toRightLinearEnd hA
             invFun := idempotentEvaluation
             left_inv := hl
             right_inv := hr
             map_mul' := map_mul (toRightLinearEnd hA)
             map_add' := map_add (toRightLinearEnd hA) }, rfl, rfl⟩
  · intro h A _ hA
    let := IdempotentedRingRightLimit.ring hA
    obtain ⟨Φ, hΦ, hΦsymm⟩ := h A hA
    constructor
    · intro x
      have h₁ := congrFun hΦ x
      have h₂ := congrFun hΦsymm (Φ x)
      simp only [RingEquiv.symm_apply_apply] at h₂
      rw [← h₁, ← h₂]
    · intro β
      have h₁ := congrFun hΦsymm β
      have h₂ := congrFun hΦ (Φ.symm β)
      simp only [RingEquiv.apply_symm_apply] at h₂
      rw [← h₁, ← h₂]

/-- The inverse identities and the uniformity comparison give a uniform isomorphism for
the named uniformities, whose two functions are the fixed maps. -/
example (h₁ : IdempotentedRingEndomorphismInverseIdentities.{uA})
    (h₃ : IdempotentedRingEndomorphismUniformityComparison.{uA})
    (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    ∃ Ψ : @UniformEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
        (IdempotentedRingRightLimit.uniformSpace A) (rightLinearEndUniformSpace A),
      ⇑(@UniformEquiv.toEquiv _ _ (IdempotentedRingRightLimit.uniformSpace A)
          (rightLinearEndUniformSpace A) Ψ) = ⇑(toRightLinearEnd hA) ∧
        ⇑(@UniformEquiv.toEquiv _ _ (IdempotentedRingRightLimit.uniformSpace A)
          (rightLinearEndUniformSpace A) Ψ).symm = ⇑(idempotentEvaluation (A := A)) := by
  obtain ⟨hl, hr⟩ := h₁ A hA
  have hcomap := h₃ A hA
  have hf : @UniformContinuous (IdempotentedRingRightLimit A) (RightLinearEnd A)
      (IdempotentedRingRightLimit.uniformSpace A) (rightLinearEndUniformSpace A)
      (toRightLinearEnd hA) := by
    rw [← hcomap]
    exact @uniformContinuous_comap _ _ _ (rightLinearEndUniformSpace A)
  have hcomp : (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A) ∘
      (idempotentEvaluation : RightLinearEnd A → IdempotentedRingRightLimit A) = id :=
    funext hr
  have hg : @UniformContinuous (RightLinearEnd A) (IdempotentedRingRightLimit A)
      (rightLinearEndUniformSpace A) (IdempotentedRingRightLimit.uniformSpace A)
      idempotentEvaluation := by
    rw [← hcomap]
    apply @uniformContinuous_comap' _ _ _ _ _ (rightLinearEndUniformSpace A)
      (rightLinearEndUniformSpace A)
    rw [hcomp]
    exact @uniformContinuous_id _ (rightLinearEndUniformSpace A)
  exact ⟨@UniformEquiv.mk _ _ (IdempotentedRingRightLimit.uniformSpace A)
      (rightLinearEndUniformSpace A)
      ⟨toRightLinearEnd hA, idempotentEvaluation, hl, hr⟩ hf hg, rfl, rfl⟩

/-- The uniformity comparison gives the source's topological statement: the topology
induced along the actual forward map is the family topology. -/
example (h₃ : IdempotentedRingEndomorphismUniformityComparison.{uA})
    (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) :
    TopologicalSpace.induced
        (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
        (rightLinearEndUniformSpace A).toTopologicalSpace =
      (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace := by
  rw [← h₃ A hA]
  rfl

/-- The closure identity implies closedness for the same ambient topology. -/
example : IdempotentedRingEndomorphismClosureLemma.{uA} →
    IdempotentedRingEndomorphismRightLinearClosed.{uA} := by
  intro h A _ hA
  rw [← h A hA]
  exact @isClosed_closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace _

end Consistency

/-! Specializations of the aggregate at universes 0 and 1, with complete bodies. -/

section Specializations

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    ∀ (A : Type) [NonUnitalRing A] (hA : IsIdempotented A),
      (∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
        ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β :=
  h.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    ∀ (A : Type) [NonUnitalRing A] (hA : IsIdempotented A),
      ∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
          (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _,
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
          ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
            ⇑(idempotentEvaluation (A := A)) :=
  h.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    ∀ (A : Type) [NonUnitalRing A] (hA : IsIdempotented A),
      UniformSpace.comap
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (rightLinearEndUniformSpace A) =
        IdempotentedRingRightLimit.uniformSpace A :=
  h.2.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    ∀ (A : Type) [NonUnitalRing A], IsIdempotented A →
      @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h.2.2.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    ∀ (A : Type) [NonUnitalRing A], IsIdempotented A →
      @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
          (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h.2.2.2.2

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    ∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
      (∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
        ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β :=
  h.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    ∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
      ∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
          (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _,
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
          ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
            ⇑(idempotentEvaluation (A := A)) :=
  h.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    ∀ (A : Type 1) [NonUnitalRing A] (hA : IsIdempotented A),
      UniformSpace.comap
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (rightLinearEndUniformSpace A) =
        IdempotentedRingRightLimit.uniformSpace A :=
  h.2.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    ∀ (A : Type 1) [NonUnitalRing A], IsIdempotented A →
      @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h.2.2.2.1

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    ∀ (A : Type 1) [NonUnitalRing A], IsIdempotented A →
      @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
          (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h.2.2.2.2

/-- A concrete ring in universe 0 and its lift to universe 1. -/
example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) :
    @closure (AddMonoid.End ℤ) (pointwiseUniformSpace ℤ).toTopologicalSpace
        (Set.range (leftMultiplication (A := ℤ) : ℤ → AddMonoid.End ℤ)) =
      (rightLinearEnd ℤ : Set (AddMonoid.End ℤ)) :=
  h.2.2.2.2 ℤ (IsIdempotented.of_ring ℤ)

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) :
    UniformSpace.comap
        (toRightLinearEnd (IsIdempotented.of_ring (ULift.{1} ℤ)) :
          IdempotentedRingRightLimit (ULift.{1} ℤ) → RightLinearEnd (ULift.{1} ℤ))
        (rightLinearEndUniformSpace (ULift.{1} ℤ)) =
      IdempotentedRingRightLimit.uniformSpace (ULift.{1} ℤ) :=
  h.2.2.1 (ULift.{1} ℤ) (IsIdempotented.of_ring (ULift.{1} ℤ))

/-- The zero ring `PUnit` is included; its endomorphism ring is trivial. -/
example (h : IdempotentedRingEndomorphismComparisonTheorem.{uA}) :
    letI := IdempotentedRingRightLimit.ring (IsIdempotented.of_ring PUnit.{uA + 1})
    ∃ Φ : IdempotentedRingRightLimit PUnit.{uA + 1} ≃+* RightLinearEnd PUnit.{uA + 1},
      ⇑Φ = ⇑(toRightLinearEnd (IsIdempotented.of_ring PUnit.{uA + 1})) ∧
        ⇑Φ.symm = ⇑(idempotentEvaluation (A := PUnit.{uA + 1})) :=
  h.2.1 PUnit.{uA + 1} (IsIdempotented.of_ring PUnit.{uA + 1})

end Specializations

/-! Competing structures cannot replace any of the specified constructions. -/

section CompetingStructures

variable {A : Type uA} [NonUnitalRing A]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingFamilyUniformity : UniformSpace (IdempotentedRingRightLimit A)]
  [competingValueUniformity : UniformSpace A]
  [competingFunctionUniformity : UniformSpace (A → A)]
  [competingEndUniformity : UniformSpace (AddMonoid.End A)]
  [competingSubringUniformity : UniformSpace (RightLinearEnd A)]

example (h : IdempotentedRingEndomorphismInverseIdentities.{uA}) (hA : IsIdempotented A) :
    (∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
      ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β :=
  h A hA

example (h : IdempotentedRingEndomorphismRingEquivalence.{uA}) (hA : IsIdempotented A) :
    ∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
        (IdempotentedRingRightLimit.ring hA).toMul _
        (IdempotentedRingRightLimit.ring hA).toAdd _,
      ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
          ⇑(idempotentEvaluation (A := A)) :=
  h A hA

example (h : IdempotentedRingEndomorphismUniformityComparison.{uA}) (hA : IsIdempotented A) :
    @UniformSpace.comap (IdempotentedRingRightLimit A) (RightLinearEnd A)
        (toRightLinearEnd hA) (rightLinearEndUniformSpace A) =
      IdempotentedRingRightLimit.uniformSpace A :=
  h A hA

example (h : IdempotentedRingEndomorphismRightLinearClosed.{uA}) (hA : IsIdempotented A) :
    @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
      (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h A hA

example (h : IdempotentedRingEndomorphismClosureLemma.{uA}) (hA : IsIdempotented A) :
    @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
      (rightLinearEnd A : Set (AddMonoid.End A)) :=
  h A hA

end CompetingStructures

/-! The same competing structures at universes 0 and 1: the aggregate still yields all
five complete component bodies for the named constructions. -/

section CompetingStructuresZero

variable {A : Type} [NonUnitalRing A]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingFamilyUniformity : UniformSpace (IdempotentedRingRightLimit A)]
  [competingValueUniformity : UniformSpace A]
  [competingFunctionUniformity : UniformSpace (A → A)]
  [competingEndUniformity : UniformSpace (AddMonoid.End A)]
  [competingSubringUniformity : UniformSpace (RightLinearEnd A)]

example (h : IdempotentedRingEndomorphismComparisonTheorem.{0}) (hA : IsIdempotented A) :
    ((∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
        ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β) ∧
      (∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
          (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _,
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
          ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
            ⇑(idempotentEvaluation (A := A))) ∧
      UniformSpace.comap
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (rightLinearEndUniformSpace A) =
        IdempotentedRingRightLimit.uniformSpace A ∧
      @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (rightLinearEnd A : Set (AddMonoid.End A)) ∧
      @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
          (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  ⟨h.1 A hA, h.2.1 A hA, h.2.2.1 A hA, h.2.2.2.1 A hA, h.2.2.2.2 A hA⟩

end CompetingStructuresZero

section CompetingStructuresOne

variable {A : Type 1} [NonUnitalRing A]
  [competingFamilyRing : Ring (IdempotentedRingRightLimit A)]
  [competingFamilyUniformity : UniformSpace (IdempotentedRingRightLimit A)]
  [competingValueUniformity : UniformSpace A]
  [competingFunctionUniformity : UniformSpace (A → A)]
  [competingEndUniformity : UniformSpace (AddMonoid.End A)]
  [competingSubringUniformity : UniformSpace (RightLinearEnd A)]

example (h : IdempotentedRingEndomorphismComparisonTheorem.{1}) (hA : IsIdempotented A) :
    ((∀ x : IdempotentedRingRightLimit A, idempotentEvaluation (toRightLinearEnd hA x) = x) ∧
        ∀ β : RightLinearEnd A, toRightLinearEnd hA (idempotentEvaluation β) = β) ∧
      (∃ Φ : @RingEquiv (IdempotentedRingRightLimit A) (RightLinearEnd A)
          (IdempotentedRingRightLimit.ring hA).toMul _
          (IdempotentedRingRightLimit.ring hA).toAdd _,
        ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ) = ⇑(toRightLinearEnd hA) ∧
          ⇑(@RingEquiv.toEquiv _ _ (IdempotentedRingRightLimit.ring hA).toMul _
            (IdempotentedRingRightLimit.ring hA).toAdd _ Φ).symm =
            ⇑(idempotentEvaluation (A := A))) ∧
      UniformSpace.comap
          (toRightLinearEnd hA : IdempotentedRingRightLimit A → RightLinearEnd A)
          (rightLinearEndUniformSpace A) =
        IdempotentedRingRightLimit.uniformSpace A ∧
      @IsClosed (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
        (rightLinearEnd A : Set (AddMonoid.End A)) ∧
      @closure (AddMonoid.End A) (pointwiseUniformSpace A).toTopologicalSpace
          (Set.range (leftMultiplication (A := A) : A → AddMonoid.End A)) =
        (rightLinearEnd A : Set (AddMonoid.End A)) :=
  ⟨h.1 A hA, h.2.1 A hA, h.2.2.1 A hA, h.2.2.2.1 A hA, h.2.2.2.2 A hA⟩

end CompetingStructuresOne

end Langlands.Algebra
