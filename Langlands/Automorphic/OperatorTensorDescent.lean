import Langlands.Automorphic.OperatorSubquotientFreeEquiv
import Langlands.Representation.Tensor.FiniteSlotDensity
import Langlands.Representation.Tensor.FiniteSlotEmbedding

/-! # Automorphic descent for a tensor with prescribed slot actions -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace Langlands.Automorphic

open Langlands.Global Langlands.FiniteTensor

variable {ι : Type*} [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] {G : ι → Type*}

/-- The designated operators act only on their designated slots. -/
def HasTensorSlotActions {M : Type*} [Monoid M]
    (ρ : Representation ℂ M (⨂[ℂ] i, V i))
    (op : ∀ i, G i → Module.End ℂ (V i)) (lift : ∀ i, G i → M) : Prop :=
  ∀ i g, ρ (lift i g) = slotAlgebraHom i (op i g)

/-- An action that contains the dense algebras of all individual tensor factors
is irreducible. It suffices to lift their generators to the acting monoid. -/
theorem tensor_isIrreducible_of_slot_density [Fintype ι] {M : Type*} [Monoid M]
    (ρ : Representation ℂ M (⨂[ℂ] i, V i))
    (op : ∀ i, G i → Module.End ℂ (V i)) (lift : ∀ i, G i → M)
    (hslot : HasTensorSlotActions ρ op lift)
    (hne : ∀ i, Nontrivial (V i))
    (hdense : ∀ i (s : Finset (V i)) (T : Module.End ℂ (V i)),
      ∃ A ∈ Algebra.adjoin ℂ (Set.range (op i)), ∀ x ∈ s, A x = T x) :
    ρ.IsIrreducible := by
  have : Nontrivial (⨂[ℂ] i, V i) := nontrivial_piTensorProduct hne
  refine { toNontrivial := ⟨⟨⊥, ⊤, ?_⟩⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h' : (⊥ : Submodule ℂ (⨂[ℂ] i, V i)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · intro W
    by_cases hbot : W.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
    obtain ⟨x, hx, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    refine eq_top_of_slot_density W.toSubmodule (fun i => Set.range (op i)) ?_ hdense hx hxne
    rintro i _ ⟨g, rfl⟩ y hy
    rw [← hslot i g]
    exact W.apply_mem_toSubmodule (lift i g) hy

private theorem slotEmbeddings_of_equiv [Finite ι] {M W : Type*} [Monoid M]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ M W}
    {ρ : Representation ℂ M (⨂[ℂ] i, V i)}
    {op : ∀ i, G i → Module.End ℂ (V i)} {lift : ∀ i, G i → M}
    (hslot : HasTensorSlotActions ρ op lift)
    (hne : ∀ i, Nontrivial (V i)) (e : σ.Equiv ρ) (i : ι) :
    ∃ j : V i →ₗ[ℂ] W, Function.Injective j ∧
      ∀ g x, j (op i g x) = σ (lift i g) (j x) := by
  obtain ⟨j, hj, hmap⟩ := exists_slotEmbedding i (fun j _ => hne j)
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ j, e.symm.toLinearEquiv.injective.comp hj, ?_⟩
  intro g x
  change e.symm (j (op i g x)) = σ (lift i g) (e.symm (j x))
  rw [← hmap (op i g) x]
  have h := Representation.IntertwiningMap.isIntertwining ρ σ
    e.symm.toIntertwiningMap (lift i g) (j x)
  rw [hslot i g] at h
  exact h

variable {F : Type*} [Field F] [NumberField F] {r : ℕ}

local instance operatorTensorDescentRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance operatorTensorDescentContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance operatorTensorDescentSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance operatorTensorDescentFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance operatorTensorDescentStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F (r + 1)) := Submodule.addCommGroup _

set_option maxHeartbeats 800000 in
/-- A simple tensor quotient for the common free operators descends to a
single actual automorphic subquotient containing all the given factors. -/
theorem exists_irreducibleOperatorSubquotient_with_slotEmbeddings [Finite ι]
    (ρ : Representation ℂ (FreeOperatorAlgebra F (r + 1)) (⨂[ℂ] i, V i))
    (op : ∀ i, G i → Module.End ℂ (V i)) (lift : ∀ i, G i → FreeOperatorAlgebra F (r + 1))
    (hslot : HasTensorSlotActions ρ op lift)
    (hne : ∀ i, Nontrivial (V i)) (hirr : ρ.IsIrreducible)
    (S : Subrepresentation
      ((stableAutomorphicAction F (r + 1)).comp (freeOperatorProjection F (r + 1)).toMonoidHom))
    (f : S.toRepresentation.IntertwiningMap ρ) (hf : Function.Surjective f) :
    ∃ Q : IrreducibleOperatorSubquotient F r, ∀ i,
      ∃ j : V i →ₗ[ℂ] Q.Space, Function.Injective j ∧
        ∀ g x, j (op i g x) = Q.subquotient.freeRepresentation (lift i g) (j x) := by
  let π : FreeOperatorAlgebra F (r + 1) →* automorphicOperatorAlgebra F (r + 1) :=
    (freeOperatorProjection F (r + 1)).toMonoidHom
  have hπ : Function.Surjective π := freeOperatorProjection_surjective F (r + 1)
  have he : ∃ Q : IrreducibleOperatorSubquotient F r,
      Nonempty (Representation.Equiv (Q.subquotient.representation.comp π) ρ) := by
    exact exists_irreducibleOperatorSubquotient_with_pullbackEquiv (F := F) (r := r)
      (A := FreeOperatorAlgebra F (r + 1)) (V := ⨂[ℂ] i, V i) (ρ := ρ) π hπ hirr S f hf
  obtain ⟨Q, ⟨e⟩⟩ := he
  exact ⟨Q, slotEmbeddings_of_equiv hslot hne e⟩

end Langlands.Automorphic
