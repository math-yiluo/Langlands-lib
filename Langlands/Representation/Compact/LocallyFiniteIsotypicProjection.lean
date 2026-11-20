import Langlands.Representation.CompactCoefficient.ConditionalProjection
import Langlands.Representation.KFiniteDual

/-! # Compact-type projections on weakly continuous locally finite representations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.KFiniteDual.IsotypicProjection

open _root_.Representation

section Modules

variable (R : Type*) [Ring R]
  (M S : Type*) [AddCommGroup M] [Module R M] [AddCommGroup S] [Module R S]
  [IsSemisimpleModule R M] [IsSimpleModule R S]

/-- The sum of the other isotypic components. -/
def complement : Submodule R M :=
  sSup (isotypicComponents R M \ {isotypicComponent R M S})

private theorem mem_components_of_ne_bot (h : isotypicComponent R M S ≠ ⊥) :
    isotypicComponent R M S ∈ isotypicComponents R M :=
  mem_isotypicComponents_iff.mpr
    ⟨IsIsotypic.isotypicComponent R M S, Submodule.IsFullyInvariant.isotypicComponent R M S, h⟩

theorem isCompl_complement :
    IsCompl (isotypicComponent R M S) (complement R M S) := by
  by_cases h : isotypicComponent R M S = ⊥
  · have heq : complement R M S = ⊤ := by
      unfold complement
      rw [h, ← sSup_isotypicComponents R M]
      congr 1
      exact Set.ext fun C =>
        ⟨fun hC => hC.1, fun hC => ⟨hC, fun he => (bot_lt_isotypicComponents hC).ne' he⟩⟩
    rw [h, heq]
    exact isCompl_bot_top
  · exact KFiniteDual.isCompl_isotypicComponent ⟨_, mem_components_of_ne_bot R M S h⟩

/-- Project onto the specified isotypic component. -/
def projection : Module.End R M :=
  (isotypicComponent R M S).projection (complement R M S) (isCompl_complement R M S)

theorem range_projection : (projection R M S).range = isotypicComponent R M S :=
  Submodule.range_projection (isCompl_complement R M S)

theorem projection_idempotent : IsIdempotentElem (projection R M S) :=
  Submodule.isIdempotentElem_projection (isCompl_complement R M S)

variable {R M S} {N T : Type*} [AddCommGroup N] [Module R N] [IsSemisimpleModule R N]
  [AddCommGroup T] [Module R T] [IsSimpleModule R T]

omit [IsSemisimpleModule R N] in
private theorem equiv_of_eq_component (h : isotypicComponent R N T = isotypicComponent R N S)
    (hne : isotypicComponent R N T ≠ ⊥) : Nonempty (T ≃ₗ[R] S) := by
  obtain ⟨U, hU, hsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le (isotypicComponent R N T)).resolve_left hne
  have ⟨eT⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R N T)
    U hU
  have ⟨eS⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R N S)
    U (h ▸ hU)
  exact ⟨eT.symm.trans eS⟩

omit [IsSemisimpleModule R M] in
private theorem complement_le_comap (f : M →ₗ[R] N) :
    complement R M S ≤ (complement R N S).comap f := by
  refine sSup_le fun C hC => ?_
  obtain ⟨T, hT, hCT⟩ := hC.1
  subst C
  have hne := hC.2
  let := hT
  let J := isotypicComponent R N T
  refine (f.le_comap_isotypicComponent T).trans (Submodule.comap_mono ?_)
  change J ≤ complement R N S
  by_cases hJ : J = ⊥
  · rw [hJ]
    exact bot_le
  · refine le_sSup ⟨mem_components_of_ne_bot R N T hJ, ?_⟩
    intro h
    have ⟨e⟩ := equiv_of_eq_component (R := R) (N := N) h hJ
    exact hne (e.isotypicComponent_eq (M := M))

/-- Module homomorphisms commute with the specified isotypic projection. -/
theorem projection_natural (f : M →ₗ[R] N) (x : M) :
    f (projection R M S x) = projection R N S (f x) :=
  projection_natural_of_mapsTo (isCompl_complement R M S) (isCompl_complement R N S) f
    (f.le_comap_isotypicComponent S) (complement_le_comap f) x

theorem projection_mem_of_mem (P : Submodule R M) {x : M} (hx : x ∈ P) :
    projection R M S x ∈ P := by
  have heq : (projection R P S ⟨x, hx⟩).val = projection R M S x :=
    projection_natural (S := S) P.subtype ⟨x, hx⟩
  exact heq ▸ (projection R P S ⟨x, hx⟩).property

end Modules

section Representations

variable {K : Type*} [Group K]
  {V W U : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  (τ : Representation ℂ K U) [τ.IsIrreducible]
  (ρ : Representation ℂ K V) [IsSemisimpleModule (MonoidAlgebra ℂ K) ρ.asModule]

/-- The isotypic projection as an actual linear intertwiner for the compact action. -/
def intertwiner : ρ.IntertwiningMap ρ :=
  (IntertwiningMap.equivLinearMapAsModule ρ ρ).symm
    (projection (MonoidAlgebra ℂ K) ρ.asModule τ.asModule)

theorem intertwiner_range :
    (intertwiner τ ρ).toLinearMap.range = CompactSplitting.isotypicPart τ ρ := by
  rw [CompactSplitting.isotypicPart_eq_map_modulePart,
    CompactSplitting.range_intertwining_eq_map_module_range, intertwiner,
    LinearEquiv.apply_symm_apply, range_projection]
  rfl

theorem intertwiner_idempotent :
    IsIdempotentElem (intertwiner τ ρ).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun f : Module.End (MonoidAlgebra ℂ K) ρ.asModule =>
    ρ.asModuleEquiv (f (ρ.asModuleEquiv.symm x)))
    (projection_idempotent (MonoidAlgebra ℂ K) ρ.asModule τ.asModule).eq

/-- The projection lies in every compact-invariant subspace containing its input. -/
theorem intertwiner_mem_of_mem (P : Subrepresentation ρ) {x : V} (hx : x ∈ P) :
    intertwiner τ ρ x ∈ P :=
  projection_mem_of_mem (S := τ.asModule) P.asSubmodule hx

variable {ρ} {σ : Representation ℂ K W} [IsSemisimpleModule (MonoidAlgebra ℂ K) σ.asModule]

theorem intertwiner_natural (f : ρ.IntertwiningMap σ) (x : V) :
    f (intertwiner τ ρ x) = intertwiner τ σ (f x) := by
  let F := IntertwiningMap.equivLinearMapAsModule ρ σ f
  exact congrArg σ.asModuleEquiv (projection_natural (S := τ.asModule) F
    (ρ.asModuleEquiv.symm x))

end Representations

end Langlands.KFiniteDual.IsotypicProjection
