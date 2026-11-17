import Langlands.Representation.Aubert.General.InductionFiniteLengthReflection
import Langlands.Representation.Twist.SubquotientProof
import Mathlib.Order.Hom.Bounded

/-! # Irreducibility reflected by actual smooth induction -/

noncomputable section

universe uR uG uV

namespace Langlands.Induction

private theorem simpleOrder_of_embedding {α β : Type*}
    [PartialOrder α] [BoundedOrder α] [PartialOrder β] [BoundedOrder β]
    (e : α ↪o β) (hb : e ⊥ = ⊥) (ht : e ⊤ = ⊤)
    [IsSimpleOrder β] : IsSimpleOrder α where
  exists_pair_ne := ⟨⊥, ⊤, fun h => IsSimpleOrder.bot_ne_top
    (α := β) (hb.symm.trans ((congrArg e h).trans ht))⟩
  eq_bot_or_eq_top S := by
    rcases eq_bot_or_eq_top (e S) with h | h
    · exact Or.inl (e.injective (h.trans hb.symm))
    · exact Or.inr (e.injective (h.trans ht.symm))

variable {R : Type uR} [Field R]
  {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [WeaklyLocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (P : Subgroup G) (σ : Representation R P V)

omit [WeaklyLocallyCompactSpace G] in
@[simp] theorem coefficientSubrepresentation_bot :
    coefficientSubrepresentation P σ ⊥ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hf x
  · exact bot_le

omit [WeaklyLocallyCompactSpace G] in
@[simp] theorem coefficientSubrepresentation_top :
    coefficientSubrepresentation P σ ⊤ = ⊤ := by
  apply top_unique
  intro f _ x
  exact Submodule.mem_top

/-- Taking induced functions valued in an invariant subspace preserves both
endpoints of the invariant-subspace lattice. -/
def coefficientSubrepresentationBoundedOrderHom :
    BoundedOrderHom (Subrepresentation σ) (Subrepresentation (smoothInduced P σ)) where
  toFun := coefficientSubrepresentation P σ
  monotone' := fun _ _ h _ hf x => h (hf x)
  map_bot' := coefficientSubrepresentation_bot P σ
  map_top' := coefficientSubrepresentation_top P σ

/-- Smooth induction reflects irreducibility of its smooth coefficient
representation. No irreducibility of the induction is inferred conversely. -/
theorem isIrreducible_of_smoothInduced (hσ : IsSmooth σ)
    (h : (smoothInduced P σ).IsIrreducible) : σ.IsIrreducible := by
  let := h
  exact simpleOrder_of_embedding (coefficientSubrepresentationOrderEmbedding P σ hσ)
    (coefficientSubrepresentation_bot P σ) (coefficientSubrepresentation_top P σ)

end Langlands.Induction

namespace Langlands.Aubert.General

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (A : SmoothRep.{0, uG, uV} ℂ M)

@[simp] theorem inducingSubrepresentationOrderEmbedding_bot :
    inducingSubrepresentationOrderEmbedding h hU A ⊥ = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  rfl

@[simp] theorem inducingSubrepresentationOrderEmbedding_top :
    inducingSubrepresentationOrderEmbedding h hU A ⊤ = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  rfl

/-- Irreducibility of actual normalized parabolic induction implies
irreducibility of the input representation. -/
theorem isIrreducible_of_normalizedInduction (hproj : Continuous h.projection)
    (hIA : ((normalizedInductionFunctor h hU).obj A).IsIrreducible) :
    A.IsIrreducible := by
  have hsm : IsSmooth (inducingRepresentation h hU A) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)).mpr
      (isSmooth_comp h.projection hproj A.isSmooth)
  have hcoeff := Induction.isIrreducible_of_smoothInduced P
    (inducingRepresentation h hU A) hsm hIA
  let := hcoeff
  exact Induction.simpleOrder_of_embedding (inducingSubrepresentationOrderEmbedding h hU A)
    (inducingSubrepresentationOrderEmbedding_bot h hU A)
    (inducingSubrepresentationOrderEmbedding_top h hU A)

end Langlands.Aubert.General
