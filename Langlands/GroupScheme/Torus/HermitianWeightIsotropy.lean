import Langlands.GroupScheme.Examples.HermitianIsotropicDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.Preorder.Finite

/-! # Isotropic subspaces from generating Hermitian weights -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianWeights

variable {I : Type u} {d : Type v} [Fintype I] [Fintype d]

/-- A finite family of lattice vectors has a subfamily containing no opposite
pair and representing every nonzero member up to sign. -/
theorem exists_nonopposite_subfamily (weights : d → I → ℤ) :
    ∃ s : Finset d,
      (∀ i ∈ s, ∀ j ∈ s, weights i + weights j ≠ 0) ∧
      ∀ j, weights j = 0 ∨ ∃ i ∈ s, weights j = weights i ∨ weights j = -weights i := by
  classical
  let P : Finset d → Prop :=
    fun s => ∀ i ∈ s, ∀ j ∈ s, weights i + weights j ≠ 0
  obtain ⟨s, hs, hmax⟩ :=
    (Set.toFinite {s : Finset d | P s}).exists_maximal
      (show {s : Finset d | P s}.Nonempty from ⟨∅, by simp [P]⟩)
  refine ⟨s, hs, ?_⟩
  intro j
  by_cases hj : weights j = 0
  · exact Or.inl hj
  right
  by_contra h
  have hneg : ∀ i ∈ s, weights j ≠ -weights i := by
    intro i hi hji
    exact h ⟨i, hi, Or.inr hji⟩
  have hself : weights j + weights j ≠ 0 := by
    intro hz
    apply hj
    funext i
    change weights j i = 0
    have hi : weights j i + weights j i = 0 := by
      simpa only [Pi.add_apply, Pi.zero_apply] using congrFun hz i
    omega
  have hp : P (insert j s) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with haj | ha
    · subst a
      rcases Finset.mem_insert.mp hb with hbj | hb
      · subst b
        exact hself
      · exact fun hz => hneg b hb (eq_neg_of_add_eq_zero_left hz)
    · rcases Finset.mem_insert.mp hb with hbj | hb
      · subst b
        exact fun hz => hneg a ha (eq_neg_of_add_eq_zero_right hz)
      · exact hs a ha b hb
  have hjmem : j ∈ s := hmax hp (Finset.subset_insert j s) (Finset.mem_insert_self j s)
  exact h ⟨j, hjmem, Or.inl rfl⟩

/-- Any finite subfamily representing a generating lattice family up to sign
has at least the rank of that lattice. -/
theorem card_le_of_generators_up_to_sign (weights : d → I → ℤ)
    (hgen : AddSubgroup.closure (Set.range weights) = ⊤) (s : Finset d)
    (hs : ∀ j, weights j = 0 ∨
      ∃ i ∈ s, weights j = weights i ∨ weights j = -weights i) :
    Fintype.card I ≤ s.card := by
  classical
  have hspan : Submodule.span ℤ (Set.range weights) = ⊤ := by
    rw [← AddSubgroup.toIntSubmodule_closure, hgen]
    rfl
  let Z := Submodule.span ℤ (weights '' (s : Set d))
  have hsub : Set.range weights ⊆ Z := by
    rintro _ ⟨j, rfl⟩
    rcases hs j with hj | ⟨i, hi, hj | hj⟩
    · rw [hj]
      exact Z.zero_mem
    · rw [hj]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · rw [hj]
      exact Z.neg_mem (Submodule.subset_span ⟨i, hi, rfl⟩)
  have htop : Z = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_le.mpr hsub
  have himage : (s.image weights : Set (I → ℤ)) = weights '' (s : Set d) := by
    simp
  have hdim := finrank_span_finset_le_card (R := ℤ) (s.image weights)
  change Module.finrank ℤ (Submodule.span ℤ (s.image weights : Set (I → ℤ))) ≤
    (s.image weights).card at hdim
  rw [himage, show Submodule.span ℤ (weights '' (s : Set d)) = ⊤ from htop,
    finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  exact hdim.trans Finset.card_image_le

variable {L : Type u} [Field L] {V : Type w} [AddCommGroup V] [Module L V]
    {σ : L →+* L}

/-- The subspace spanned by a selected finite subfamily of a weight basis. -/
def selectedWeightSpan (b : Module.Basis d L V) (s : Finset d) : Submodule L V :=
  Submodule.span L (b '' (s : Set d))

/-- A generating weight basis, with pairing zero away from opposite weights,
contains an actual totally isotropic subspace at least as large as the
rank of the weight lattice. -/
theorem exists_isotropic_of_weightBasis
    (h : V →ₗ[L] V →ₛₗ[σ] L) (b : Module.Basis d L V)
    (weights : d → I → ℤ)
    (hgen : AddSubgroup.closure (Set.range weights) = ⊤)
    (horth : ∀ i j, weights i + weights j ≠ 0 → h (b i) (b j) = 0) :
    ∃ W : Submodule L V,
      (∀ a b : W, h (a : V) (b : V) = 0) ∧
      Fintype.card I ≤ Module.finrank L W := by
  classical
  obtain ⟨s, hs, hcover⟩ := exists_nonopposite_subfamily weights
  let W := selectedWeightSpan b s
  have hfirst : ∀ i ∈ s, ∀ z ∈ W, h (b i) z = 0 := by
    intro i hi z hz
    have hle : W ≤ (h (b i)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      exact horth i j (hs i hi j hj)
    exact hle hz
  have hboth : ∀ a b : W, h (a : V) (b : V) = 0 := by
    intro a z
    have hle : W ≤ (h.flip (z : V)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact hfirst i hi z z.property
    exact hle a.property
  have hdim : Module.finrank L W = s.card := by
    have hli := (b.linearIndependent.linearIndepOn (s : Set d)).id_image
    have himage : (s.image b : Set V) = b '' (s : Set d) := by simp
    change Module.finrank L (Submodule.span L (b '' (s : Set d))) = s.card
    rw [← himage, finrank_span_finset_eq_card (himage.symm ▸ hli)]
    exact Finset.card_image_of_injective s b.injective
  exact ⟨W, hboth, hdim ▸ card_le_of_generators_up_to_sign weights hgen s hcover⟩

end Langlands.GroupScheme.HermitianWeights
