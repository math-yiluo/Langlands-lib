import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuples

/-! # Reindexing finite related tuples -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u})

/-- The unique map realizing a pairwise related family of scheme-valued points. -/
noncomputable def tupleLift (n : ℕ) {T : Scheme.{u}}
    (a : Fin (n + 1) → (T ⟶ E.U))
    (h : ∀ i j, ∃ r : T ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j) :
    T ⟶ E.tupleScheme n :=
  (E.exists_tuple_lift n a h).choose

@[reassoc (attr := simp)]
lemma tupleLift_projection (n : ℕ) {T : Scheme.{u}}
    (a : Fin (n + 1) → (T ⟶ E.U))
    (h : ∀ i j, ∃ r : T ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (i : Fin (n + 1)) :
    E.tupleLift n a h ≫ E.tupleProjection n i = a i :=
  (E.exists_tuple_lift n a h).choose_spec i

lemma tupleLift_unique (n : ℕ) {T : Scheme.{u}}
    (a : Fin (n + 1) → (T ⟶ E.U))
    (h : ∀ i j, ∃ r : T ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (f : T ⟶ E.tupleScheme n)
    (hf : ∀ i, f ≫ E.tupleProjection n i = a i) :
    f = E.tupleLift n a h := by
  apply E.tuple_hom_ext n
  intro i
  simp [hf]

/-- Precomposition of a canonical tuple lift is the canonical lift of the
precomposed coordinates. -/
lemma comp_tupleLift (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T)
    (a : Fin (n + 1) → (T ⟶ E.U))
    (h : ∀ i j, ∃ r : T ⟶ E.R, r ≫ E.t = a i ∧ r ≫ E.s = a j)
    (h' : ∀ i j, ∃ r : S ⟶ E.R,
      r ≫ E.t = f ≫ a i ∧ r ≫ E.s = f ≫ a j) :
    f ≫ E.tupleLift n a h = E.tupleLift n (fun i => f ≫ a i) h' := by
  apply E.tupleLift_unique n
  intro i
  simp

/-- A map of index sets gives a contravariant morphism of related-tuple schemes. -/
noncomputable def tupleReindex {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) :
    E.tupleScheme n ⟶ E.tupleScheme m :=
  E.tupleLift m (fun i => E.tupleProjection n (a i))
    (fun i j => E.tupleProjection_related n (a i) (a j))

@[reassoc (attr := simp)]
lemma tupleReindex_projection {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (i : Fin (m + 1)) :
    E.tupleReindex a ≫ E.tupleProjection m i = E.tupleProjection n (a i) :=
  E.tupleLift_projection _ _ _ _

@[simp] lemma tupleReindex_id (n : ℕ) :
    E.tupleReindex (id : Fin (n + 1) → Fin (n + 1)) =
      𝟙 (E.tupleScheme n) := by
  apply E.tuple_hom_ext n
  intro i
  simp

@[reassoc]
lemma tupleReindex_comp {l m n : ℕ}
    (a : Fin (l + 1) → Fin (m + 1)) (b : Fin (m + 1) → Fin (n + 1)) :
    E.tupleReindex b ≫ E.tupleReindex a = E.tupleReindex (b ∘ a) := by
  apply E.tuple_hom_ext l
  intro i
  simp

/-- Bijections of index sets induce isomorphisms of tuple schemes.
In particular, permutations act by permuting coordinates. -/
noncomputable def tupleReindexIso {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) :
    E.tupleScheme n ≅ E.tupleScheme m where
  hom := E.tupleReindex a
  inv := E.tupleReindex a.symm
  hom_inv_id := by
    apply E.tuple_hom_ext n
    intro i
    simp
  inv_hom_id := by
    apply E.tuple_hom_ext m
    intro i
    simp

@[reassoc (attr := simp)]
lemma tupleReindexIso_hom_projection {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (m + 1)) :
    (E.tupleReindexIso a).hom ≫ E.tupleProjection m i =
      E.tupleProjection n (a i) :=
  E.tupleReindex_projection a i

@[reassoc (attr := simp)]
lemma tupleReindexIso_inv_projection {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    (E.tupleReindexIso a).inv ≫ E.tupleProjection n i =
      E.tupleProjection m (a.symm i) :=
  E.tupleReindex_projection a.symm i

@[simp] lemma tupleReindexIso_refl (n : ℕ) :
    E.tupleReindexIso (Equiv.refl (Fin (n + 1))) =
      Iso.refl (E.tupleScheme n) := by
  apply Iso.ext
  apply E.tuple_hom_ext n
  intro i
  simp

@[simp] lemma tupleReindexIso_symm {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) :
    E.tupleReindexIso a.symm = (E.tupleReindexIso a).symm := rfl

lemma tupleReindexIso_trans {l m n : ℕ}
    (a : Fin (l + 1) ≃ Fin (m + 1)) (b : Fin (m + 1) ≃ Fin (n + 1)) :
    (E.tupleReindexIso b) ≪≫ (E.tupleReindexIso a) =
      E.tupleReindexIso (a.trans b) := by
  apply Iso.ext
  apply E.tuple_hom_ext l
  intro i
  simp

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
