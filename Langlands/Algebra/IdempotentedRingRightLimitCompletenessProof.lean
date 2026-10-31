import Langlands.Algebra.IdempotentedRingRightLimitCompletenessStatements

/-!
# Density and completeness of the actual right-image inverse limit

The completeness exercise of Renard I.1.3 is proved by closedness in
the full product of discrete original carriers. Density uses the
source's actual coordinate approximation.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Set
open scoped Topology

universe uA

variable {A : Type uA} [NonUnitalRing A]

/-- Both defining families of compatibility equations are closed equalizers. -/
theorem idempotentedRingRightLimit_closedFamily (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitClosedFamily A := by
  let : UniformSpace A := ⊥
  change IsClosed {x : Idempotent A → A |
    (∀ e, x e * (e : A) = x e) ∧
      ∀ e f, e ≤ f → x f * (e : A) = x e}
  simp_rw [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro e
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (fun a : A => a * (e : A))).comp
        (continuous_apply e))
      (continuous_apply e)
  · apply isClosed_iInter
    intro e
    apply isClosed_iInter
    intro f
    apply isClosed_iInter
    intro _
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (fun a : A => a * (e : A))).comp
        (continuous_apply f))
      (continuous_apply e)

/-- The actual uniformity is exactly that on the closed subset of a complete product. -/
theorem idempotentedRingRightLimit_complete (A : Type uA) [NonUnitalRing A] :
    IdempotentedRingRightLimitComplete A := by
  let : UniformSpace A := ⊥
  change @CompleteSpace (IdempotentedRingRightLimit A)
    (IdempotentedRingRightLimit.uniformSpace A)
  rw [IdempotentedRingRightLimit.uniformSpace_eq_subtype A]
  have hc : IsClosed (rightCompatibleFamilies A : Set (Idempotent A → A)) :=
    idempotentedRingRightLimit_closedFamily A
  exact hc.isComplete.completeSpace_coe

/-- Every coordinate neighborhood contains the canonical image of that coordinate value. -/
theorem idempotentedRingRightLimit_canonicalDense (hA : IsIdempotented A) :
    IdempotentedRingRightLimitCanonicalDense A := by
  let := IdempotentedRingRightLimit.uniformSpace A
  intro x
  apply (mem_closure_iff_nhds_basis (IdempotentedRingRightLimit.nhds_hasBasis hA x)).mpr
  intro e _
  refine ⟨IdempotentedRingRightLimit.canonical (x.val e), ⟨x.val e, rfl⟩, ?_⟩
  exact x.property.1 e

/-- Density and the exact canonical pullback give a dense topological embedding. -/
theorem idempotentedRingRightLimit_canonicalDenseEmbedding (hA : IsIdempotented A) :
    IdempotentedRingRightLimitCanonicalDenseEmbedding A := by
  let := idempotentedRingUniformSpace A
  let := IdempotentedRingRightLimit.uniformSpace A
  let : TopologicalSpace A := (idempotentedRingUniformSpace A).toTopologicalSpace
  let : TopologicalSpace (IdempotentedRingRightLimit A) :=
    (IdempotentedRingRightLimit.uniformSpace A).toTopologicalSpace
  exact
    { toIsDenseInducing :=
        { toIsInducing := (IdempotentedRingRightLimit.isUniformInducing_canonical A).isInducing
          dense := idempotentedRingRightLimit_canonicalDense hA }
      injective := IdempotentedRingRightLimit.canonical_injective hA }

/-- The exact closed target for actual right-image families and original canonical maps. -/
theorem idempotentedRingRightLimitDensityCompletenessTheorem_proof :
    IdempotentedRingRightLimitDensityCompletenessTheorem.{uA} := by
  intro A _
  refine ⟨idempotentedRingRightLimit_closedFamily A,
    idempotentedRingRightLimit_complete A, ?_⟩
  intro hA
  exact ⟨idempotentedRingRightLimit_canonicalDense hA,
    idempotentedRingRightLimit_canonicalDenseEmbedding hA⟩

/-! Complete unapplied proof interfaces at the arbitrary original-ring universe. -/

example : (A : Type uA) → [NonUnitalRing A] →
    IdempotentedRingRightLimitClosedFamily A :=
  idempotentedRingRightLimit_closedFamily.{uA}

example : (A : Type uA) → [NonUnitalRing A] →
    IdempotentedRingRightLimitComplete A :=
  idempotentedRingRightLimit_complete.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimitCanonicalDense A :=
  @idempotentedRingRightLimit_canonicalDense.{uA}

example : {A : Type uA} → [NonUnitalRing A] → IsIdempotented A →
    IdempotentedRingRightLimitCanonicalDenseEmbedding A :=
  @idempotentedRingRightLimit_canonicalDenseEmbedding.{uA}

end Langlands.Algebra
