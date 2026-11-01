import Mathlib.Order.Zorn

/-! # Strict partial cocycle atlases and their maximal extensions -/

universe u v

noncomputable section

namespace Langlands.CategoryTheory.StrictCocycleAtlas

/-- A vertex or an actual transition with specified endpoints. -/
inductive Label {I : Type u} (T : I → I → Type v) : Type (max u v)
  | vertex (i : I)
  | edge (i j : I) (e : T i j)

variable {I : Type u} {T : I → I → Type v}

/-- A partial atlas has a distinguished chart, exactly one transition for each
ordered pair of its charts, and the prescribed triple compatibility. -/
def Good (C : ∀ i j k, T i j → T j k → T i k → Prop) (i₀ : I)
    (S : Set (Label T)) : Prop :=
  Label.vertex i₀ ∈ S ∧
    (∀ i j e, Label.edge i j e ∈ S →
      Label.vertex i ∈ S ∧ Label.vertex j ∈ S) ∧
    (∀ i j, Label.vertex i ∈ S → Label.vertex j ∈ S →
      ∃ e, Label.edge i j e ∈ S) ∧
    (∀ i j e e', Label.edge i j e ∈ S → Label.edge i j e' ∈ S → e = e') ∧
    (∀ i j k eij ejk eik,
      Label.edge i j eij ∈ S → Label.edge j k ejk ∈ S →
        Label.edge i k eik ∈ S → C i j k eij ejk eik)

variable {C : ∀ i j k, T i j → T j k → T i k → Prop} {i₀ : I}
  {S : Set (Label T)}

/-- The charts present in a label set. -/
def domain (S : Set (Label T)) : Set I := {i | Label.vertex i ∈ S}

/-- The unique transition selected from a good atlas. -/
def transition (h : Good C i₀ S) (i j : domain S) : T i.val j.val :=
  Classical.choose (h.2.2.1 i.val j.val i.property j.property)

lemma transition_mem (h : Good C i₀ S) (i j : domain S) :
    Label.edge i.val j.val (transition h i j) ∈ S :=
  Classical.choose_spec (h.2.2.1 i.val j.val i.property j.property)

lemma transition_eq (h : Good C i₀ S) (i j : domain S) (e : T i.val j.val)
    (he : Label.edge i.val j.val e ∈ S) : transition h i j = e :=
  h.2.2.2.1 _ _ _ _ (transition_mem h i j) he

lemma transition_cocycle (h : Good C i₀ S) (i j k : domain S) :
    C i.val j.val k.val (transition h i j) (transition h j k) (transition h i k) :=
  h.2.2.2.2 _ _ _ _ _ _ (transition_mem h i j)
    (transition_mem h j k) (transition_mem h i k)

/-- Strict inclusion preserves every previously chosen transition. -/
lemma transition_preserved {S' : Set (Label T)} (h : Good C i₀ S)
    (h' : Good C i₀ S') (hSS' : S ⊆ S') (i j : domain S) :
    transition h' ⟨i.val, hSS' i.property⟩ ⟨j.val, hSS' j.property⟩ =
      transition h i j :=
  transition_eq h' _ _ _ (hSS' (transition_mem h i j))

private lemma pair_in_chain {α : Type*} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) {a b : α}
    (ha : a ∈ ⋃₀ c) (hb : b ∈ ⋃₀ c) :
    ∃ A ∈ c, a ∈ A ∧ b ∈ A := by
  obtain ⟨A, hAc, ha⟩ := ha
  obtain ⟨B, hBc, hb⟩ := hb
  obtain ⟨D, hDc, hAD, hBD⟩ := hc.directedOn A hAc B hBc
  exact ⟨D, hDc, hAD ha, hBD hb⟩

private lemma triple_in_chain {α : Type*} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) {a b d : α}
    (ha : a ∈ ⋃₀ c) (hb : b ∈ ⋃₀ c) (hd : d ∈ ⋃₀ c) :
    ∃ A ∈ c, a ∈ A ∧ b ∈ A ∧ d ∈ A := by
  obtain ⟨A, hAc, ha, hb⟩ := pair_in_chain hc ha hb
  obtain ⟨B, hBc, hd⟩ := hd
  obtain ⟨D, hDc, hAD, hBD⟩ := hc.directedOn A hAc B hBc
  exact ⟨D, hDc, hAD ha, hAD hb, hBD hd⟩

/-- A nonempty chain has an upper bound preserving its actual transition labels. -/
lemma good_sUnion {c : Set (Set (Label T))} (hne : c.Nonempty)
    (hc : IsChain (· ⊆ ·) c) (hg : ∀ A ∈ c, Good C i₀ A) :
    Good C i₀ (⋃₀ c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨A, hAc⟩ := hne
    exact ⟨A, hAc, (hg A hAc).1⟩
  · intro i j e he
    obtain ⟨A, hAc, he⟩ := he
    obtain ⟨hi, hj⟩ := (hg A hAc).2.1 i j e he
    exact ⟨⟨A, hAc, hi⟩, ⟨A, hAc, hj⟩⟩
  · intro i j hi hj
    obtain ⟨A, hAc, hi, hj⟩ := pair_in_chain hc hi hj
    obtain ⟨e, he⟩ := (hg A hAc).2.2.1 i j hi hj
    exact ⟨e, A, hAc, he⟩
  · intro i j e e' he he'
    obtain ⟨A, hAc, he, he'⟩ := pair_in_chain hc he he'
    exact (hg A hAc).2.2.2.1 i j e e' he he'
  · intro i j k eij ejk eik hij hjk hik
    obtain ⟨A, hAc, hij, hjk, hik⟩ := triple_in_chain hc hij hjk hik
    exact (hg A hAc).2.2.2.2 i j k eij ejk eik hij hjk hik

/-- Every good atlas has a maximal strict extension. -/
lemma exists_maximal_extension (h : Good C i₀ S) :
    ∃ M : Set (Label T), S ⊆ M ∧ Maximal (Good C i₀) M := by
  apply zorn_subset_nonempty {A | Good C i₀ A} ?_ S h
  intro c hcg hc hne
  exact ⟨⋃₀ c, good_sUnion hne hc hcg, fun A hAc ↦ Set.subset_sUnion_of_mem hAc⟩

/-- A chosen maximal strict extension of a given good atlas. -/
def maximalExtension (h : Good C i₀ S) : Set (Label T) :=
  Classical.choose (exists_maximal_extension h)

lemma subset_maximalExtension (h : Good C i₀ S) : S ⊆ maximalExtension h :=
  (Classical.choose_spec (exists_maximal_extension h)).1

lemma maximalExtension_maximal (h : Good C i₀ S) :
    Maximal (Good C i₀) (maximalExtension h) :=
  (Classical.choose_spec (exists_maximal_extension h)).2

/-- The full set of vertices and transitions associated to a fixed chart family. -/
def graph (A : Set I) (t : ∀ i j : A, T i.val j.val) : Set (Label T)
  | .vertex i => i ∈ A
  | .edge i j e => ∃ hi : i ∈ A, ∃ hj : j ∈ A, e = t ⟨i, hi⟩ ⟨j, hj⟩

lemma graph_good (A : Set I) (t : ∀ i j : A, T i.val j.val) (hi₀ : i₀ ∈ A)
    (ht : ∀ i j k : A, C i.val j.val k.val (t i j) (t j k) (t i k)) :
    Good C i₀ (graph A t) := by
  refine ⟨hi₀, ?_, ?_, ?_, ?_⟩
  · rintro i j e ⟨hi, hj, _⟩
    exact ⟨hi, hj⟩
  · intro i j hi hj
    exact ⟨t ⟨i, hi⟩ ⟨j, hj⟩, hi, hj, rfl⟩
  · rintro i j e e' ⟨hi, hj, rfl⟩ ⟨hi', hj', rfl⟩
    rfl
  · rintro i j k eij ejk eik ⟨hi, hj, rfl⟩ ⟨hj', hk, rfl⟩ ⟨hi', hk', rfl⟩
    exact ht ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩

/-- A good atlas is exactly the graph of its selected transition family. -/
lemma graph_transition (h : Good C i₀ S) :
    graph (domain S) (transition h) = S := by
  ext l
  cases l with
  | vertex i => rfl
  | edge i j e =>
    constructor
    · rintro ⟨hi, hj, rfl⟩
      exact transition_mem h ⟨i, hi⟩ ⟨j, hj⟩
    · intro he
      obtain ⟨hi, hj⟩ := h.2.1 i j e he
      exact ⟨hi, hj, (transition_eq h ⟨i, hi⟩ ⟨j, hj⟩ e he).symm⟩

/-- A coherent family on a larger domain extends the old atlas when each old
transition label is retained exactly. -/
lemma subset_graph (h : Good C i₀ S) {A : Set I}
    (hA : domain S ⊆ A) (t : ∀ i j : A, T i.val j.val)
    (ht : ∀ i j : domain S,
      t ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩ = transition h i j) :
    S ⊆ graph A t := by
  intro l hl
  cases l with
  | vertex i => exact hA hl
  | edge i j e =>
    obtain ⟨hi, hj⟩ := h.2.1 i j e hl
    refine ⟨hA hi, hA hj, ?_⟩
    exact ((ht ⟨i, hi⟩ ⟨j, hj⟩).trans (transition_eq h _ _ e hl)).symm

/-- A coherent strict extension of a maximal atlas cannot add a chart. -/
lemma maximal_domain (hm : Maximal (Good C i₀) S) {A : Set I}
    (hA : domain S ⊆ A) (t : ∀ i j : A, T i.val j.val)
    (ht : ∀ i j : domain S,
      t ⟨i.val, hA i.property⟩ ⟨j.val, hA j.property⟩ = transition hm.1 i j)
    (hC : ∀ i j k : A, C i.val j.val k.val (t i j) (t j k) (t i k)) :
    A = domain S := by
  have hg : Good C i₀ (graph A t) := graph_good A t (hA hm.1.1) hC
  have hsub : graph A t ⊆ S := hm.2 hg (subset_graph hm.1 hA t ht)
  exact Set.Subset.antisymm (fun _ hi ↦ hsub hi) hA

end Langlands.CategoryTheory.StrictCocycleAtlas
