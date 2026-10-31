import Langlands.Algebra.NonUnitalModuleLeftLimitCompletenessStatements

/-!
# Closedness, density and completeness of the actual left-image module inverse limit

Renard I.1.4, printed p.9/PDF15, says that the I.1.3 arguments adapt to
modules. Closedness in the full product of discrete original carriers
gives completeness; density uses the actual coordinate approximation.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

open Set
open scoped Topology

universe uA uM

/-- Both defining families of left-compatibility equations are closed equalizers. -/
theorem nonUnitalModuleLeftLimit_closedFamily (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitClosedFamily A M := by
  let : UniformSpace M := ⊥
  change IsClosed {x : Idempotent A → M |
    (∀ e : Idempotent A, (e : A) • x e = x e) ∧
      ∀ e f : Idempotent A, e ≤ f → (e : A) • x f = x e}
  simp_rw [ofPred_and, ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro e
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (fun m : M => (e : A) • m)).comp
        (continuous_apply e))
      (continuous_apply e)
  · apply isClosed_iInter
    intro e
    apply isClosed_iInter
    intro f
    apply isClosed_iInter
    intro _
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (fun m : M => (e : A) • m)).comp
        (continuous_apply f))
      (continuous_apply e)

/-- The actual family uniformity is the subspace uniformity of a closed subset of a
complete product. -/
theorem nonUnitalModuleLeftLimit_complete (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] :
    NonUnitalModuleLeftLimitComplete A M := by
  let : UniformSpace M := ⊥
  change @CompleteSpace (NonUnitalModuleLeftLimit A M)
    (NonUnitalModuleLeftLimit.uniformSpace A M)
  rw [NonUnitalModuleLeftLimit.uniformSpace_eq_subtype A M]
  have hc : IsClosed (leftCompatibleFamilies A M : Set (Idempotent A → M)) :=
    nonUnitalModuleLeftLimit_closedFamily A M
  exact hc.isComplete.completeSpace_coe

/-- Every basic neighborhood `{y | y e = x e}` contains the canonical image of `x e`. -/
theorem nonUnitalModuleLeftLimit_canonicalDense {A : Type uA} {M : Type uM}
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M] (hA : IsIdempotented A) :
    NonUnitalModuleLeftLimitCanonicalDense A M := by
  let := NonUnitalModuleLeftLimit.uniformSpace A M
  intro x
  apply (mem_closure_iff_nhds_basis (NonUnitalModuleLeftLimit.nhds_hasBasis hA x)).mpr
  intro e _
  refine ⟨NonUnitalModuleLeftLimit.canonical (x.val e), ⟨x.val e, rfl⟩, ?_⟩
  exact x.property.1 e

/-- Density, the exact canonical pullback and injectivity give a dense embedding. -/
theorem nonUnitalModuleLeftLimit_canonicalDenseEmbedding {A : Type uA} {M : Type uM}
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M) :
    NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M := by
  -- Both topologies are passed explicitly: with the original uniformity installed on `M`,
  -- instance search would pick the (different) subtype topology on the family carrier.
  have hi : @Topology.IsInducing M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M).toTopologicalSpace
      (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace
      (NonUnitalModuleLeftLimit.canonical (A := A) (M := M)) :=
    @IsUniformInducing.isInducing M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M) (NonUnitalModuleLeftLimit.uniformSpace A M) _
      (NonUnitalModuleLeftLimit.isUniformInducing_canonical A M)
  exact @IsDenseEmbedding.mk M (NonUnitalModuleLeftLimit A M)
    (nonUnitalModuleUniformSpace A M).toTopologicalSpace
    (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _
    (@IsDenseInducing.mk M (NonUnitalModuleLeftLimit A M)
      (nonUnitalModuleUniformSpace A M).toTopologicalSpace
      (NonUnitalModuleLeftLimit.uniformSpace A M).toTopologicalSpace _
      hi (nonUnitalModuleLeftLimit_canonicalDense hA))
    (NonUnitalModuleLeftLimit.canonical_injective hM)

/-- The exact closed target for actual left-image families and original canonical maps. -/
theorem nonUnitalModuleLeftLimitDensityCompletenessTheorem_proof :
    NonUnitalModuleLeftLimitDensityCompletenessTheorem.{uA, uM} := by
  intro A M _ _ _
  exact ⟨nonUnitalModuleLeftLimit_closedFamily A M, nonUnitalModuleLeftLimit_complete A M,
    fun hA => nonUnitalModuleLeftLimit_canonicalDense hA,
    fun hA hM => nonUnitalModuleLeftLimit_canonicalDenseEmbedding hA hM⟩

/-! Complete unapplied proof interfaces at independent ring/vector universes. -/

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleLeftLimitClosedFamily A M :=
  nonUnitalModuleLeftLimit_closedFamily.{uA, uM}

example : (A : Type uA) → (M : Type uM) →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] →
    NonUnitalModuleLeftLimitComplete A M :=
  nonUnitalModuleLeftLimit_complete.{uA, uM}

example : {A : Type uA} → {M : Type uM} →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    NonUnitalModuleLeftLimitCanonicalDense A M :=
  @nonUnitalModuleLeftLimit_canonicalDense.{uA, uM}

example : {A : Type uA} → {M : Type uM} →
    [NonUnitalRing A] → [AddCommGroup M] → [NonUnitalModule A M] → IsIdempotented A →
    IsNondegenerate A M → NonUnitalModuleLeftLimitCanonicalDenseEmbedding A M :=
  @nonUnitalModuleLeftLimit_canonicalDenseEmbedding.{uA, uM}

example : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{0, 1} :=
  nonUnitalModuleLeftLimitDensityCompletenessTheorem_proof.{0, 1}

example : NonUnitalModuleLeftLimitDensityCompletenessTheorem.{1, 0} :=
  nonUnitalModuleLeftLimitDensityCompletenessTheorem_proof.{1, 0}

end Langlands.Algebra
