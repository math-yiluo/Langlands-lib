import Langlands.Global.AdelicWeylSetAssociation
import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Global.AdelicIntertwiningOperator
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Composition and inversion in the Weyl sets `Ω(P, P')`

For parabolics `P = MU` with Levi projections `π : P → M` (`l ≫ π = 𝟙`), Weyl conjugations
`(w, c)` compose and invert, and the induced parameter maps compose accordingly. Consequently,
for a finite family of parabolics with enumerations `T i i'` of `Ω(P i, P i')`,
`|Ω(P i, P i')| = |Ω(P i', P i)|`, and `|Ω(P i, P i'')| = |Ω(P i', P i'')|` for every `i''`
whenever `Ω(P i', P i)` is nonempty, so `n_P i = ∑ i', |Ω(P i, P i')|` is constant on
association classes. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G P P' P'' M M' M'' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {p' : P' ⟶ G} {p'' : P'' ⟶ G} {l : M ⟶ P} {l' : M' ⟶ P'} {l'' : M'' ⟶ P''}

theorem innerIso_one_inv : (G.innerIso (1 : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)).inv =
    𝟙 G := by
  rw [← cancel_epi (G.innerIso 1).hom, Iso.hom_inv_id, innerIso_one_hom, Category.comp_id]

/-- The composite of two Weyl conjugations `P' → P → P''` is a Weyl conjugation `P' → P''`. -/
theorem IsWeylConjugation.trans {w w₀ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    {c : M'' ⟶ M} {c₀ : M ⟶ M'} (h : IsWeylConjugation p l p'' l'' w c)
    (h₀ : IsWeylConjugation p' l' p l w₀ c₀) :
    IsWeylConjugation p' l' p'' l'' (w * w₀) (c ≫ c₀) := by
  have := h.isIso
  have := h₀.isIso
  refine ⟨inferInstance, ?_⟩
  rw [Category.assoc, h₀.comp_eq, reassoc_of% h.comp_eq, innerIso_mul_inv]

/-- The inverse of a Weyl conjugation. -/
theorem IsWeylConjugation.symm {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    {c : M' ⟶ M} (h : IsWeylConjugation p l p' l' w c) :
    ∃ c' : M ⟶ M', c ≫ c' = 𝟙 M' ∧ c' ≫ c = 𝟙 M ∧ IsWeylConjugation p' l' p l w⁻¹ c' := by
  have := h.isIso
  refine ⟨inv c, IsIso.hom_inv_id c, IsIso.inv_hom_id c, ⟨inferInstance, ?_⟩⟩
  rw [IsIso.inv_comp_eq, innerIso_inv_point_inv, reassoc_of% h.comp_eq]
  simp

/-- Composition of parameter maps: for `l ≫ π = 𝟙`,
`weylParameter l c π'' ∘ weylParameter l' c₀ π = weylParameter l' (c ≫ c₀) π''`. -/
theorem weylParameter_comp_of_retraction {π : P ⟶ M} (hlπ : l ≫ π = 𝟙 M) (c : M'' ⟶ M) (π'' : P'' ⟶ M'')
    (c₀ : M ⟶ M') :
    (weylParameter (F := F) l c π'').comp (weylParameter l' c₀ π) =
      weylParameter l' (c ≫ c₀) π'' := by
  exact weylParameter_comp l' c₀ π l c π'' hlπ

section Families

variable {I : Type*} {P M : I → GroupScheme (Spec (CommRingCat.of F))}
  {p : ∀ i, P i ⟶ G} {l : ∀ i, M i ⟶ P i} {π : ∀ i, P i ⟶ M i}
  (hlπ : ∀ i, l i ≫ π i = 𝟙 (M i))
  (T : I → I → Type*) [∀ i i', Fintype (T i i')]
  (w : ∀ i i', T i i' → (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X))
  (cw : ∀ i i', T i i' → (M i' ⟶ M i))
  (hW : ∀ i i' t, IsWeylConjugation (p i) (l i) (p i') (l i') (w i i' t) (cw i i' t))
  (hinj : ∀ i i', Function.Injective (fun t => weylParameter (l i) (cw i i' t) (π i')))
  (hsurj : ∀ i i', ∀ s ∈ weylParameterSet (p i) (l i) (p i') (l i') (π i'),
    ∃ t, weylParameter (l i) (cw i i' t) (π i') = s)

include hlπ hW hinj hsurj

/-- `|Ω(P i, P i'')| ≤ |Ω(P i', P i'')|` when `Ω(P i', P i)` is nonempty: composing with a fixed
element of `Ω(P i', P i)` is injective. -/
theorem card_le_card_of_weylConjugation {i i' : I} (t₀ : T i' i) (i'' : I) :
    Fintype.card (T i i'') ≤ Fintype.card (T i' i'') := by
  obtain ⟨c₀', hc₀, -, -⟩ := (hW i' i t₀).symm
  have hmem : ∀ t : T i i'', weylParameter (l i') (cw i i'' t ≫ cw i' i t₀) (π i'') ∈
      weylParameterSet (p i') (l i') (p i'') (l i'') (π i'') := fun t =>
    ⟨_, _, (hW i i'' t).trans (hW i' i t₀), rfl⟩
  choose φ hφ using fun t => hsurj i' i'' _ (hmem t)
  refine Fintype.card_le_of_injective φ fun t₁ t₂ h => hinj i i'' ?_
  have h' := congrArg (fun s => s.comp (weylParameter (l i) c₀' (π i'))) (by
    rw [← hφ t₁, ← hφ t₂, h] :
      weylParameter (l i') (cw i i'' t₁ ≫ cw i' i t₀) (π i'') =
        weylParameter (l i') (cw i i'' t₂ ≫ cw i' i t₀) (π i''))
  simp only [weylParameter_comp_of_retraction (hlπ i'), Category.assoc, hc₀, Category.comp_id] at h'
  exact h'

/-- `|Ω(P i, P i'')| = |Ω(P i', P i'')|` when `Ω(P i', P i)` is nonempty. -/
theorem card_eq_card_of_weylConjugation {i i' : I} (t₀ : T i' i) (i'' : I) :
    Fintype.card (T i i'') = Fintype.card (T i' i'') := by
  refine le_antisymm (card_le_card_of_weylConjugation hlπ T w cw hW hinj hsurj t₀ i'') ?_
  obtain ⟨c₀', -, hc₀', h₀'⟩ := (hW i' i t₀).symm
  have hmem : ∀ t : T i' i'', weylParameter (l i) (cw i' i'' t ≫ c₀') (π i'') ∈
      weylParameterSet (p i) (l i) (p i'') (l i'') (π i'') := fun t =>
    ⟨_, _, (hW i' i'' t).trans h₀', rfl⟩
  choose φ hφ using fun t => hsurj i i'' _ (hmem t)
  refine Fintype.card_le_of_injective φ fun t₁ t₂ h => hinj i' i'' ?_
  have h' := congrArg (fun s => s.comp (weylParameter (l i') (cw i' i t₀) (π i))) (by
    rw [← hφ t₁, ← hφ t₂, h] :
      weylParameter (l i) (cw i' i'' t₁ ≫ c₀') (π i'') =
        weylParameter (l i) (cw i' i'' t₂ ≫ c₀') (π i''))
  simp only [weylParameter_comp_of_retraction (hlπ i), Category.assoc, hc₀', Category.comp_id] at h'
  exact h'

/-- `|Ω(P i, P i')| ≤ |Ω(P i', P i)|`: inverting Weyl conjugations is injective. -/
theorem card_le_card_swap (i i' : I) : Fintype.card (T i i') ≤ Fintype.card (T i' i) := by
  choose c' hc hc' hW' using fun t : T i i' => (hW i i' t).symm
  have hmem : ∀ t, weylParameter (l i') (c' t) (π i) ∈
      weylParameterSet (p i') (l i') (p i) (l i) (π i) := fun t => ⟨_, _, hW' t, rfl⟩
  choose φ hφ using fun t => hsurj i' i _ (hmem t)
  refine Fintype.card_le_of_injective φ fun t₁ t₂ h => hinj i i' ?_
  have hu : weylParameter (l i') (c' t₁) (π i) = weylParameter (l i') (c' t₂) (π i) := by
    rw [← hφ t₁, ← hφ t₂, h]
  have e1 : ∀ t, (weylParameter (l i') (c' t) (π i)).comp
      (weylParameter (l i) (cw i i' t) (π i')) = weylParameter (l i) (𝟙 (M i)) (π i) :=
    fun t => by rw [weylParameter_comp_of_retraction (hlπ i'), hc' t]
  have e2 : ∀ t, (weylParameter (l i) (cw i i' t) (π i')).comp
      (weylParameter (l i) (𝟙 (M i)) (π i)) = weylParameter (l i) (cw i i' t) (π i') :=
    fun t => by rw [weylParameter_comp_of_retraction (hlπ i), Category.comp_id]
  have e3 : ∀ t, (weylParameter (l i) (cw i i' t) (π i')).comp
      (weylParameter (l i') (c' t) (π i)) = weylParameter (l i') (𝟙 (M i')) (π i') :=
    fun t => by rw [weylParameter_comp_of_retraction (hlπ i), hc t]
  have e4 : ∀ t, (weylParameter (l i') (𝟙 (M i')) (π i')).comp
      (weylParameter (l i) (cw i i' t) (π i')) = weylParameter (l i) (cw i i' t) (π i') :=
    fun t => by rw [weylParameter_comp_of_retraction (hlπ i'), Category.id_comp]
  show weylParameter (l i) (cw i i' t₁) (π i') = weylParameter (l i) (cw i i' t₂) (π i')
  rw [← e2 t₁, ← e1 t₂, ← LinearMap.comp_assoc, ← hu, e3, e4]

/-- `|Ω(P i, P i')| = |Ω(P i', P i)|`. -/
theorem card_swap (i i' : I) : Fintype.card (T i i') = Fintype.card (T i' i) :=
  le_antisymm (card_le_card_swap hlπ T w cw hW hinj hsurj i i')
    (card_le_card_swap hlπ T w cw hW hinj hsurj i' i)

omit [∀ i i', Fintype (T i i')] hlπ hW hinj in
/-- `Ω(P i, P i)` contains the identity, so it is enumerated by a nonempty type. -/
theorem nonempty_self (i : I) : Nonempty (T i i) := by
  have h1 : IsWeylConjugation (p i) (l i) (p i) (l i) 1 (𝟙 (M i)) :=
    ⟨inferInstance, by rw [innerIso_one_inv, Category.id_comp, Category.comp_id]⟩
  obtain ⟨t, -⟩ := hsurj i i _ ⟨1, 𝟙 (M i), h1, rfl⟩
  exact ⟨t⟩

/-- Arthur's normalization: with `n_P i = ∑ i', |Ω(P i, P i')|`,
`∑ i', |Ω(P i', P i)| / n_P i' = 1` for every `i`. -/
theorem sum_card_div_card_eq_one [Fintype I] (i : I) :
    ∑ i', (Fintype.card (T i' i) : ℂ) / (∑ i'', Fintype.card (T i' i'') : ℕ) = 1 := by
  have hn : ∀ i', Nonempty (T i' i) →
      (∑ i'', Fintype.card (T i' i'') : ℕ) = ∑ i'', Fintype.card (T i i'') := fun i' ⟨t₀⟩ =>
    Finset.sum_congr rfl fun i'' _ =>
      (card_eq_card_of_weylConjugation hlπ T w cw hW hinj hsurj t₀ i'').symm
  have hterm : ∀ i', (Fintype.card (T i' i) : ℂ) / (∑ i'', Fintype.card (T i' i'') : ℕ) =
      (Fintype.card (T i' i) : ℂ) / (∑ i'', Fintype.card (T i i'') : ℕ) := by
    intro i'
    rcases isEmpty_or_nonempty (T i' i) with h | h
    · simp [Fintype.card_eq_zero]
    · rw [hn i' h]
  have hpos : (∑ i'', Fintype.card (T i i'') : ℕ) ≠ 0 := by
    have := nonempty_self T cw hsurj i
    exact (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨i, Finset.mem_univ _, Fintype.card_pos⟩).ne'
  simp_rw [hterm, ← Finset.sum_div]
  rw [div_eq_one_iff_eq (by exact_mod_cast hpos)]
  push_cast
  exact Finset.sum_congr rfl fun i' _ => by
    rw [card_swap hlπ T w cw hW hinj hsurj i' i]

end Families

end Langlands.Global.AdelicGroupPoints
