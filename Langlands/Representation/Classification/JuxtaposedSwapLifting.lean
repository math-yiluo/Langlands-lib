import Langlands.Representation.Classification.Segments
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Group.GL.AdjacentMergeShape

/-!
# Lifting an adjacent two-block swap along a uniform shape

For the uniform shape `(r, …, r)` with `N` blocks and a family `σ` of
representations of `GL_r`, an isomorphism `σ_j × σ_{j+1} ≅ σ_{j+1} × σ_j` of
two-block products lifts to an isomorphism between the products of `σ` and of
`σ ∘ (j j+1)`. Both products are regrouped over the shape merging the blocks `j`
and `j + 1`; outside the merged block the inner families agree, and at the merged
block the inner product is the given two-block product.
-/

noncomputable section

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A two-block uniform product, written over any shape with two blocks of size `r`,
inherits an isomorphism between the two orders of its factors. -/
theorem merged_swap {r : ℕ} (hr : 0 < r)
    (σa σb : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (h2 : letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![σa, σb] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![σb, σa]))
    (L n₀ : ℕ) (pos : ∀ _ : Fin L, 0 < r) (se : ∑ _ : Fin L, r = n₀) (hL : L = 2)
    (τ τ' : letI := T.topology
      Fin L → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (h0 : ∀ k : Fin L, k.val = 0 → τ k = σa ∧ τ' k = σb)
    (h1 : ∀ k : Fin L, k.val = 1 → τ k = σb ∧ τ' k = σa) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        ({ length := L, size := fun _ => r, positive := pos, sum_eq := se } :
          BlockShape n₀)).obj τ ≅
      (T.normalizedProductInductionFunctor.{uF, uV}
        ({ length := L, size := fun _ => r, positive := pos, sum_eq := se } :
          BlockShape n₀)).obj τ') := by
  let := T.topology
  subst hL
  have hn : n₀ = 2 * r := by rw [← se]; simp
  subst hn
  have hτ : τ = ![σa, σb] := by
    funext k
    match k with
    | ⟨0, _⟩ => exact (h0 _ rfl).1
    | ⟨1, _⟩ => exact (h1 _ rfl).1
  have hτ' : τ' = ![σb, σa] := by
    funext k
    match k with
    | ⟨0, _⟩ => exact (h0 _ rfl).2
    | ⟨1, _⟩ => exact (h1 _ rfl).2
  subst hτ hτ'
  exact h2

/-- Regroup a uniform product over the shape merging the blocks `j` and `j + 1`. -/
theorem uniform_regroup {N r : ℕ} (hr : 0 < r) (j : ℕ) (h : j + 1 < N)
    (σ : letI := T.topology
      Fin N → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform N r hr)).obj σ ≅
      (T.normalizedProductInductionFunctor.{uF, max uF uV}
        ((BlockShape.uniform N r hr).adjacentMerge j h)).obj (fun m =>
          (T.normalizedProductInductionFunctor.{uF, uV}
            ((BlockShape.uniform N r hr).adjacentRefinement j h m)).obj
            (fun k => σ ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨m, k⟩)))) := by
  let := T.topology
  obtain ⟨e⟩ := Parabolic.orderedProductRegrouping.{uF, uV} F T (N * r)
    (BlockShape.uniform N r hr) ((BlockShape.uniform N r hr).adjacentMerge j h)
    ((BlockShape.uniform N r hr).adjacentRefinement j h)
    ((BlockShape.uniform N r hr).adjacentBlockEquiv j h) (fun _ => rfl)
    ((BlockShape.uniform N r hr).adjacent_index j h) σ
  dsimp only at e
  exact ⟨e⟩

/-- Lift an isomorphism of the two orders of the factors `σ_j`, `σ_{j+1}` to the
products of `σ` and of `σ ∘ (j j+1)` along the uniform shape `(r, …, r)`. -/
theorem uniform_adjacentSwap {N r : ℕ} (hr : 0 < r)
    (σ : letI := T.topology
      Fin N → SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (j : ℕ) (h : j + 1 < N)
    (h2 : letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![σ ⟨j, by omega⟩, σ ⟨j + 1, h⟩] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj ![σ ⟨j + 1, h⟩, σ ⟨j, by omega⟩])) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform N r hr)).obj σ ≅
      (T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform N r hr)).obj
        (fun i => σ (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩ i))) := by
  let := T.topology
  let sw : Equiv.Perm (Fin N) := Equiv.swap ⟨j, by omega⟩ ⟨j + 1, h⟩
  have hfib : ∀ m : Fin ((BlockShape.uniform N r hr).adjacentMerge j h).length,
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          ((BlockShape.uniform N r hr).adjacentRefinement j h m)).obj
          (fun k => σ ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨m, k⟩)) ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          ((BlockShape.uniform N r hr).adjacentRefinement j h m)).obj
          (fun k => σ (sw ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨m, k⟩)))) := by
    intro m
    have hv : ∀ k, @Fin.val N ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨m, k⟩) =
        m.val + k.val + if j < m.val then 1 else 0 := fun k =>
      (BlockShape.uniform N r hr).adjacentBlockEquiv_val j h ⟨m, k⟩
    by_cases hm : m.val = j
    · obtain rfl : m = (BlockShape.uniform N r hr).adjacentMergeIndex j h := Fin.ext hm
      refine merged_swap hr (σ ⟨j, by omega⟩) (σ ⟨j + 1, h⟩) h2 _ _ _ _
        ((BlockShape.uniform N r hr).adjacentRefinement_length_merged j h) _ _ ?_ ?_
      · intro k hk
        have he : @Eq (Fin N)
            ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨_, k⟩) ⟨j, by omega⟩ :=
          Fin.ext ((hv k).trans (by rw [hm, hk]; simp))
        refine ⟨congrArg σ he, ?_⟩
        rw [he]
        exact congrArg σ (Equiv.swap_apply_left _ _)
      · intro k hk
        have he : @Eq (Fin N)
            ((BlockShape.uniform N r hr).adjacentBlockEquiv j h ⟨_, k⟩) ⟨j + 1, h⟩ :=
          Fin.ext ((hv k).trans (by rw [hm, hk]; simp))
        refine ⟨congrArg σ he, ?_⟩
        rw [he]
        exact congrArg σ (Equiv.swap_apply_right _ _)
    · have hfam : (fun k => σ (sw ((BlockShape.uniform N r hr).adjacentBlockEquiv j h
            ⟨m, k⟩))) = fun k => σ ((BlockShape.uniform N r hr).adjacentBlockEquiv j h
            ⟨m, k⟩) := by
        funext k
        congr 1
        have hk : k.val < 1 :=
          ((BlockShape.uniform N r hr).adjacentRefinement_length_of_ne j h m hm) ▸ k.isLt
        have hvk := hv k
        apply Equiv.swap_apply_of_ne_of_ne
        · intro hh
          have := congrArg Fin.val hh
          rw [hvk] at this
          dsimp only at this
          split_ifs at this <;> omega
        · intro hh
          have := congrArg Fin.val hh
          rw [hvk] at this
          dsimp only at this
          split_ifs at this <;> omega
      rw [hfam]
      exact ⟨Iso.refl _⟩
  obtain ⟨e₀⟩ := uniform_regroup.{uF, uV} (T := T) hr j h σ
  obtain ⟨e₁⟩ := uniform_regroup.{uF, uV} (T := T) hr j h (fun i => σ (sw i))
  exact ⟨e₀ ≪≫ (T.normalizedProductInductionFunctor.{uF, max uF uV}
    ((BlockShape.uniform N r hr).adjacentMerge j h)).mapIso
    (Pi.isoMk fun m => (hfib m).some) ≪≫ e₁.symm⟩

end Langlands.Classification.JuxtaposedShuffle
