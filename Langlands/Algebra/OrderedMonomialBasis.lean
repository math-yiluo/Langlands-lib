import Langlands.Algebra.OrderedPBWBasis
import Langlands.Representation.Archimedean.LowerVermaPBW

/-! # Ordered enveloping monomials along any list of basis indices -/

noncomputable section

universe u v w

set_option autoImplicit false

namespace Langlands.Algebra.LieWeightProjection

open Langlands.Algebra.UniversalEnveloping Langlands.Archimedean.Kostant
  Langlands.Archimedean.VermaPBW

attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {L : Type v} [LieRing L] [LieAlgebra k L]
  {B : Type w} [Fintype B] [DecidableEq B] (b : Module.Basis B k L) {bs : List B}

omit [Fintype B] [DecidableEq B] in
theorem word_expand_map (α : B →₀ ℕ) (l : List B) :
    word k L ((expand l α).map b) =
      (l.map fun c => UniversalEnvelopingAlgebra.ι k (b c) ^ α c).prod := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [show expand (c :: l) α = List.replicate (α c) c ++ expand l α by
      simp [expand]]
    rw [List.map_append, word_append, ih, List.map_cons, List.prod_cons]
    congr 1
    rw [List.map_replicate]
    simp [word, List.map_replicate, List.prod_replicate]

/-- The bijection between `Fin bs.length` and the indices given by a complete
duplicate-free list. -/
def listEquiv (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) : Fin bs.length ≃ B :=
  Equiv.ofBijective bs.get ⟨List.nodup_iff_injective_get.mp hbs, fun c => by
    obtain ⟨i, hi⟩ := List.get_of_mem (hall c)
    exact ⟨i, hi⟩⟩

omit [Fintype B] [DecidableEq B] in
theorem orderedMonomial_eq_orderedPBWMonomial (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs)
    (α : B →₀ ℕ) :
    orderedMonomial k L b bs α =
      orderedPBWMonomial (b.reindex (listEquiv hbs hall).symm)
        (fun i => α (listEquiv hbs hall i)) := by
  unfold orderedMonomial
  rw [word_expand_map, orderedPBWMonomial]
  congr 1
  conv_lhs => rw [← List.ofFn_get bs]
  rw [List.map_ofFn]
  congr 1
  funext i
  rw [Module.Basis.reindex_apply, Equiv.symm_symm]
  rfl

omit [Fintype B] [DecidableEq B] in
/-- The ordered monomials along any complete duplicate-free list of basis indices are
linearly independent. -/
theorem linearIndependent_orderedMonomial_list (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) :
    LinearIndependent k (orderedMonomial k L b bs) := by
  let e := listEquiv hbs hall
  have hind := (orderedPBWBasis k L bs.length (b.reindex e.symm)).1
  let φ : (B →₀ ℕ) → (Fin bs.length → ℕ) := fun α i => α (e i)
  have hφ : Function.Injective φ := by
    intro α β h
    ext c
    have := congrFun h (e.symm c)
    simpa [φ] using this
  have heq : orderedMonomial k L b bs = orderedPBWMonomial (b.reindex e.symm) ∘ φ := by
    funext α
    exact orderedMonomial_eq_orderedPBWMonomial b hbs hall α
  rw [heq]
  exact hind.comp φ hφ

/-- The Poincaré–Birkhoff–Witt basis of ordered monomials for any complete
duplicate-free list of indices of a finite basis of a Lie algebra over a field. -/
def orderedMonomialBasis (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) :
    Module.Basis (B →₀ ℕ) k (UniversalEnvelopingAlgebra k L) :=
  Module.Basis.mk (linearIndependent_orderedMonomial_list b hbs hall)
    (top_le_span_orderedMonomial b hbs hall)

theorem orderedMonomialBasis_apply (hbs : bs.Nodup) (hall : ∀ c, c ∈ bs) (α : B →₀ ℕ) :
    orderedMonomialBasis b hbs hall α = orderedMonomial k L b bs α :=
  Module.Basis.mk_apply _ _ _

end Langlands.Algebra.LieWeightProjection
