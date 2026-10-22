import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Descending an invariant by a finite cardinality bound -/

noncomputable section

namespace Langlands.FiniteInvariantDescent

universe u v w

variable {A : Type u} {B : Type v} {D : Type w}
  [AddGroup A] [AddGroup B] [AddGroup D]
  (j : A →+ B) (s : A →+ D) (hker : j.ker ≤ s.ker)

/-- An invariant killing the kernel of `j` descends to the image of `j`. -/
def onRange : j.range →+ D :=
  j.rangeRestrict.liftOfSurjective j.rangeRestrict_surjective
    ⟨s, by simpa only [AddMonoidHom.ker_rangeRestrict] using hker⟩

@[simp]
theorem onRange_apply (a : A) : onRange j s hker (j.rangeRestrict a) = s a := by
  simp [onRange]

/-- Descent to the image preserves surjectivity of the invariant. -/
theorem onRange_surjective (hs : Function.Surjective s) :
    Function.Surjective (onRange j s hker) := by
  intro d
  obtain ⟨a, rfl⟩ := hs d
  exact ⟨j.rangeRestrict a, onRange_apply j s hker a⟩

variable [Finite B]

include hker in
/-- A surjective invariant whose target is at least as large as `B` forces `j` onto. -/
theorem surjective_of_card_le (hs : Function.Surjective s)
    (hcard : Nat.card B ≤ Nat.card D) : Function.Surjective j := by
  apply AddMonoidHom.range_eq_top.mp
  apply AddSubgroup.eq_top_of_le_card
  exact hcard.trans (Nat.card_le_card_of_surjective _ (onRange_surjective j s hker hs))

/-- The descended invariant is bijective when the same cardinality bound holds. -/
theorem onRange_bijective (hs : Function.Surjective s)
    (hcard : Nat.card B ≤ Nat.card D) : Function.Bijective (onRange j s hker) :=
  (onRange_surjective j s hker hs).bijective_of_nat_card_le
    ((Nat.card_le_card_of_injective j.range.subtype Subtype.val_injective).trans hcard)

/-- The resulting equivalence on the whole of `B`, without an assumed inverse to `j`. -/
def equiv (hs : Function.Surjective s) (hcard : Nat.card B ≤ Nat.card D) : B ≃+ D :=
  (AddEquiv.ofBijective j.range.subtype
    ⟨Subtype.val_injective, fun b => by
      obtain ⟨a, rfl⟩ := surjective_of_card_le j s hker hs hcard b
      exact ⟨j.rangeRestrict a, rfl⟩⟩).symm.trans
    (AddEquiv.ofBijective (onRange j s hker) (onRange_bijective j s hker hs hcard))

@[simp]
theorem equiv_apply (hs : Function.Surjective s) (hcard : Nat.card B ≤ Nat.card D)
    (a : A) : equiv j s hker hs hcard (j a) = s a := by
  change onRange j s hker _ = s a
  have h : (AddEquiv.ofBijective j.range.subtype
      ⟨Subtype.val_injective, fun b => by
        obtain ⟨x, rfl⟩ := surjective_of_card_le j s hker hs hcard b
        exact ⟨j.rangeRestrict x, rfl⟩⟩).symm (j a) = j.rangeRestrict a := by
    apply Subtype.ext
    exact (AddEquiv.ofBijective j.range.subtype _).apply_symm_apply (j a)
  exact (congrArg (onRange j s hker) h).trans (onRange_apply j s hker a)

/-- The whole descended invariant is characterized by its values before `j`. -/
theorem equiv_unique (hs : Function.Surjective s) (hcard : Nat.card B ≤ Nat.card D)
    (f : B →+ D) (hf : f.comp j = s) : f = (equiv j s hker hs hcard).toAddMonoidHom := by
  ext b
  obtain ⟨a, rfl⟩ := surjective_of_card_le j s hker hs hcard b
  exact (DFunLike.congr_fun hf a).trans (equiv_apply j s hker hs hcard a).symm

include hker in
/-- The cardinality argument strengthens the original kernel inclusion to equality. -/
theorem ker_eq (hs : Function.Surjective s) (hcard : Nat.card B ≤ Nat.card D) :
    j.ker = s.ker := by
  apply le_antisymm hker
  intro a ha
  apply (equiv j s hker hs hcard).injective
  simpa only [equiv_apply, map_zero] using (show s a = 0 from ha)

end Langlands.FiniteInvariantDescent
