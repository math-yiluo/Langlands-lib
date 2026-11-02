import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDistinct

/-! # Reindexing distinct related tuples -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

lemma tupleDistinctOpen_le_preimage {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (ha : Function.Injective a) :
    E.tupleDistinctOpen n ≤ E.tupleReindex a ⁻¹ᵁ E.tupleDistinctOpen m := by
  intro x hx
  change E.tupleReindex a x ∈ E.tupleDistinctOpen m
  rw [E.mem_tupleDistinctOpen] at hx ⊢
  intro i j hij heq
  apply hx (a i) (a j) (fun h => hij (ha h))
  rw [← E.tupleReindex_preimage_equalOpen a i j]
  exact heq

lemma tupleReindex_preimage_distinctOpen {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) :
    E.tupleReindex a ⁻¹ᵁ E.tupleDistinctOpen m = E.tupleDistinctOpen n := by
  apply le_antisymm
  · intro x hx
    change E.tupleReindex a x ∈ E.tupleDistinctOpen m at hx
    rw [E.mem_tupleDistinctOpen] at hx ⊢
    intro i j hij heq
    obtain ⟨i, rfl⟩ := a.surjective i
    obtain ⟨j, rfl⟩ := a.surjective j
    apply hx i j (fun h => hij (congrArg a h))
    change x ∈ E.tupleReindex a ⁻¹ᵁ E.tupleEqualOpen m i j
    rwa [E.tupleReindex_preimage_equalOpen]
  · exact E.tupleDistinctOpen_le_preimage a a.injective

/-- An injective index map selects a subtuple of distinct related coordinates. -/
noncomputable def tupleDistinctReindex {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (ha : Function.Injective a) :
    E.tupleDistinctScheme n ⟶ E.tupleDistinctScheme m :=
  (E.tupleReindex a).resLE (E.tupleDistinctOpen m) (E.tupleDistinctOpen n)
    (E.tupleDistinctOpen_le_preimage a ha)

@[reassoc (attr := simp)]
lemma tupleDistinctReindex_ι {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (ha : Function.Injective a) :
    E.tupleDistinctReindex a ha ≫ (E.tupleDistinctOpen m).ι =
      (E.tupleDistinctOpen n).ι ≫ E.tupleReindex a :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)]
lemma tupleDistinctReindex_projection {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (ha : Function.Injective a)
    (i : Fin (m + 1)) :
    E.tupleDistinctReindex a ha ≫ E.tupleDistinctProjection m i =
      E.tupleDistinctProjection n (a i) := by
  change E.tupleDistinctReindex a ha ≫
    ((E.tupleDistinctOpen m).ι ≫ E.tupleProjection m i) = _
  rw [← Category.assoc, E.tupleDistinctReindex_ι, Category.assoc, E.tupleReindex_projection]

lemma tupleDistinct_hom_ext (n : ℕ) {T : Scheme.{u}}
    {f g : T ⟶ E.tupleDistinctScheme n}
    (h : ∀ i, f ≫ E.tupleDistinctProjection n i =
      g ≫ E.tupleDistinctProjection n i) : f = g := by
  apply (cancel_mono (E.tupleDistinctOpen n).ι).mp
  apply E.tuple_hom_ext n
  intro i
  simpa [tupleDistinctProjection, Category.assoc] using h i

@[simp] lemma tupleDistinctReindex_id (n : ℕ) :
    E.tupleDistinctReindex (id : Fin (n + 1) → Fin (n + 1)) Function.injective_id =
      𝟙 (E.tupleDistinctScheme n) := by
  apply E.tupleDistinct_hom_ext n
  intro i
  simp

@[reassoc]
lemma tupleDistinctReindex_comp {l m n : ℕ}
    (a : Fin (l + 1) → Fin (m + 1)) (ha : Function.Injective a)
    (b : Fin (m + 1) → Fin (n + 1)) (hb : Function.Injective b) :
    E.tupleDistinctReindex b hb ≫ E.tupleDistinctReindex a ha =
      E.tupleDistinctReindex (b ∘ a) (hb.comp ha) := by
  apply E.tupleDistinct_hom_ext l
  intro i
  simp

/-- A bijection of index sets gives an isomorphism of distinct-tuple schemes. -/
noncomputable def tupleDistinctReindexIso {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) :
    E.tupleDistinctScheme n ≅ E.tupleDistinctScheme m where
  hom := E.tupleDistinctReindex a a.injective
  inv := E.tupleDistinctReindex a.symm a.symm.injective
  hom_inv_id := by
    apply E.tupleDistinct_hom_ext n
    intro i
    simp
  inv_hom_id := by
    apply E.tupleDistinct_hom_ext m
    intro i
    simp

@[reassoc (attr := simp)]
lemma tupleDistinctReindexIso_hom_projection {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (m + 1)) :
    (E.tupleDistinctReindexIso a).hom ≫ E.tupleDistinctProjection m i =
      E.tupleDistinctProjection n (a i) :=
  E.tupleDistinctReindex_projection a a.injective i

@[reassoc (attr := simp)]
lemma tupleDistinctReindexIso_inv_projection {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) (i : Fin (n + 1)) :
    (E.tupleDistinctReindexIso a).inv ≫ E.tupleDistinctProjection n i =
      E.tupleDistinctProjection m (a.symm i) :=
  E.tupleDistinctReindex_projection a.symm a.symm.injective i

@[simp] lemma tupleDistinctReindexIso_refl (n : ℕ) :
    E.tupleDistinctReindexIso (Equiv.refl (Fin (n + 1))) =
      Iso.refl (E.tupleDistinctScheme n) := by
  apply Iso.ext
  apply E.tupleDistinct_hom_ext n
  intro i
  simp

@[simp] lemma tupleDistinctReindexIso_symm {m n : ℕ}
    (a : Fin (m + 1) ≃ Fin (n + 1)) :
    E.tupleDistinctReindexIso a.symm = (E.tupleDistinctReindexIso a).symm := rfl

lemma tupleDistinctReindexIso_trans {l m n : ℕ}
    (a : Fin (l + 1) ≃ Fin (m + 1)) (b : Fin (m + 1) ≃ Fin (n + 1)) :
    (E.tupleDistinctReindexIso b) ≪≫ (E.tupleDistinctReindexIso a) =
      E.tupleDistinctReindexIso (a.trans b) := by
  apply Iso.ext
  apply E.tupleDistinct_hom_ext l
  intro i
  simp

/-- Coordinates of a distinct tuple remain distinct as morphisms from a nonempty
scheme. This applies in particular to geometric points. -/
lemma tupleDistinct_coordinates_injective (n : ℕ) {T : Scheme.{u}} [Nonempty T]
    (f : T ⟶ E.tupleDistinctScheme n) :
    Function.Injective (fun i => f ≫ E.tupleDistinctProjection n i) := by
  intro i j h
  by_contra hij
  have h' : Set.range (f ≫ (E.tupleDistinctOpen n).ι) ⊆ E.tupleEqualOpen n i j :=
    (E.range_subset_tupleEqualOpen_iff n i j _).mpr (by
      simpa [tupleDistinctProjection, Category.assoc] using h)
  obtain ⟨x⟩ := ‹Nonempty T›
  exact (E.mem_tupleDistinctOpen n _).mp (f x).property i j hij (h' ⟨x, rfl⟩)

/-- No nonidentity permutation fixes a distinct tuple over a nonempty scheme. -/
lemma tupleDistinctReindexIso_free (n : ℕ) {T : Scheme.{u}} [Nonempty T]
    (f : T ⟶ E.tupleDistinctScheme n) (a : Equiv.Perm (Fin (n + 1)))
    (h : f ≫ (E.tupleDistinctReindexIso a).hom = f) : a = 1 := by
  apply Equiv.ext
  intro i
  apply E.tupleDistinct_coordinates_injective n f
  have h' := congrArg (fun k => k ≫ E.tupleDistinctProjection n i) h
  simpa using h'

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
