import Langlands.Representation.Classification.SegmentProductPermutation
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-!
# Lifting an adjacent two-block isomorphism to a full segment product

For a segment-product datum `d` and adjacent positions `j`, `j + 1`, the direct and
swapped products are regrouped over the same merged outer shape. The inner data retain
the supplied actual blocks. An isomorphism of the two orders of the merged two-block
datum then gives an isomorphism of the two full products. The lifting assumes no head,
socle, linkage or irreducibility condition; head and socle witnesses are only restricted
to the inner data for later use.
-/

noncomputable section


namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace AdjacentSegmentSwapLifting

variable {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)

/-- Retain selected actual segment occurrences and their supplied blocks. -/
def select {r m : ℕ} (f : Fin r → Fin d.length)
    (hs : ∑ i, (d.segments (f i)).degree = m) :
    T.SegmentProductDatum.{max uF uV, uF} m where
  length := r
  segments i := d.segments (f i)
  degree_sum := hs
  blocks i := d.blocks (f i)

theorem select_congr {r m : ℕ} {f g : Fin r → Fin d.length}
    (hf : ∑ i, (d.segments (f i)).degree = m)
    (hg : ∑ i, (d.segments (g i)).degree = m) (he : f = g) :
    select d f hf = select d g hg := by
  subst g
  rfl

variable (j : ℕ) (h : j + 1 < d.length)

/-- The actual inner datum of the direct adjacent refinement. -/
def directFiber (m : Fin (d.shape.adjacentMerge j h).length) :
    T.SegmentProductDatum.{max uF uV, uF} ((d.shape.adjacentMerge j h).size m) :=
  select d (fun k => d.shape.adjacentBlockEquiv j h ⟨m, k⟩)
    (d.shape.adjacentRefinement j h m).sum_eq

/-- The actual inner datum of the swapped refinement in the same outer shape. -/
def swappedFiber (m : Fin (d.shape.adjacentMerge j h).length) :
    T.SegmentProductDatum.{max uF uV, uF} ((d.shape.adjacentMerge j h).size m) :=
  select d (fun k => d.shape.adjacentSwap j h
    (d.shape.adjacentSwapBlockEquiv j h ⟨m, k⟩))
    (d.shape.adjacentSwapRefinement j h m).sum_eq

@[simp] theorem directFiber_shape (m : Fin (d.shape.adjacentMerge j h).length) :
    (directFiber d j h m).shape = d.shape.adjacentRefinement j h m := rfl

@[simp] theorem swappedFiber_shape (m : Fin (d.shape.adjacentMerge j h).length) :
    (swappedFiber d j h m).shape = d.shape.adjacentSwapRefinement j h m := rfl

theorem directFiber_heads (hd : d.HasSegmentHeads)
    (m : Fin (d.shape.adjacentMerge j h).length) :
    (directFiber d j h m).HasSegmentHeads :=
  fun k => hd (d.shape.adjacentBlockEquiv j h ⟨m, k⟩)

theorem directFiber_socles (hd : d.HasSegmentSocles)
    (m : Fin (d.shape.adjacentMerge j h).length) :
    (directFiber d j h m).HasSegmentSocles :=
  fun k => hd (d.shape.adjacentBlockEquiv j h ⟨m, k⟩)

/-- Outside the merged slot, the actual inner data are equal. -/
theorem swappedFiber_eq_of_ne (m : Fin (d.shape.adjacentMerge j h).length)
    (hm : m.val ≠ j) : swappedFiber d j h m = directFiber d j h m := by
  apply select_congr
  funext k
  change d.shape.adjacentSwap j h (d.shape.adjacentBlockEquiv j h ⟨m, k⟩) =
    d.shape.adjacentBlockEquiv j h ⟨m, k⟩
  have hk : k.val < 1 := (d.shape.adjacentRefinement_length_of_ne j h m hm) ▸ k.isLt
  have hv := d.shape.adjacentBlockEquiv_val j h ⟨m, k⟩
  dsimp only at hv
  apply Equiv.swap_apply_of_ne_of_ne
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega
  · rw [ne_eq, Fin.ext_iff, hv]
    dsimp only
    split_ifs <;> omega

/-! ### The merged two-block datum -/

/-- The actual two-block datum at the merged slot: the original blocks `j` and
`j + 1`, in this order. -/
def mergedFiber :
    T.SegmentProductDatum.{max uF uV, uF}
      ((d.shape.adjacentMerge j h).size (d.shape.adjacentMergeIndex j h)) :=
  directFiber d j h (d.shape.adjacentMergeIndex j h)

theorem mergedFiber_length : (mergedFiber d j h).length = 2 :=
  d.shape.adjacentRefinement_length_merged j h

theorem mergedFiber_swap_bound : 0 + 1 < (mergedFiber d j h).length := by
  rw [mergedFiber_length]
  omega

theorem mergedFiber_label (k : Fin (mergedFiber d j h).length) :
    (d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, k⟩).val = j + k.val := by
  rw [d.shape.adjacentBlockEquiv_val j h]
  change j + k.val + (if j < j then 1 else 0) = j + k.val
  simp

theorem mergedFiber_segments_zero :
    (mergedFiber d j h).segments ⟨0, by rw [mergedFiber_length]; omega⟩ =
      d.segments ⟨j, by omega⟩ := by
  change d.segments (d.shape.adjacentBlockEquiv j h
    ⟨d.shape.adjacentMergeIndex j h, ⟨0, _⟩⟩) = _
  congr 1
  exact Fin.ext (mergedFiber_label d j h _)

theorem mergedFiber_segments_one :
    (mergedFiber d j h).segments ⟨1, by rw [mergedFiber_length]; omega⟩ =
      d.segments ⟨j + 1, h⟩ := by
  change d.segments (d.shape.adjacentBlockEquiv j h
    ⟨d.shape.adjacentMergeIndex j h, ⟨1, _⟩⟩) = _
  congr 1
  exact Fin.ext (mergedFiber_label d j h _)

/-- In the merged slot, the swapped inner datum is exactly the two-block permutation. -/
theorem swappedFiber_eq_permute :
    swappedFiber d j h (d.shape.adjacentMergeIndex j h) =
      (mergedFiber d j h).permute
        ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h)) := by
  apply select_congr
  funext k
  change d.shape.adjacentSwap j h
      (d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, k⟩) =
    d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h,
      Equiv.swap ⟨0, _⟩ ⟨1, _⟩ k⟩
  let f := fun q : Fin (mergedFiber d j h).length =>
    d.shape.adjacentBlockEquiv j h ⟨d.shape.adjacentMergeIndex j h, q⟩
  have hf : Function.Injective f := by
    intro q r hqr
    have he := (d.shape.adjacentBlockEquiv j h).injective hqr
    exact Fin.ext (congrArg (fun a => a.2.val) he)
  let a : Fin (mergedFiber d j h).length :=
    ⟨0, by rw [mergedFiber_length]; omega⟩
  let b : Fin (mergedFiber d j h).length :=
    ⟨1, by rw [mergedFiber_length]; omega⟩
  have ha : f a = ⟨j, by change j < d.length; omega⟩ :=
    Fin.ext ((mergedFiber_label d j h a).trans (Nat.add_zero j))
  have hb : f b = ⟨j + 1, h⟩ := Fin.ext (mergedFiber_label d j h b)
  have hs := hf.swap_apply a b k
  rw [ha, hb] at hs
  exact hs

/-! ### Regrouping both orders over the merged shape -/

theorem directFiber_induced (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    (directFiber d j h m).induced =
      (T.normalizedProductInductionFunctor (d.shape.adjacentRefinement j h m)).obj
        (fun k => d.blocks (d.shape.adjacentBlockEquiv j h ⟨m, k⟩)) := rfl

theorem swappedFiber_induced (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    (swappedFiber d j h m).induced =
      (T.normalizedProductInductionFunctor (d.shape.adjacentSwapRefinement j h m)).obj
        (fun k => d.blocks (d.shape.adjacentSwap j h
          (d.shape.adjacentSwapBlockEquiv j h ⟨m, k⟩))) := rfl

/-- Exact regrouping identifies the direct product with its actual inner data. -/
theorem regroup_direct :
    letI := T.topology
    Nonempty (d.induced ≅ (T.normalizedProductInductionFunctor
      (d.shape.adjacentMerge j h)).obj (fun m => (directFiber d j h m).induced)) := by
  let := T.topology
  have hh := Parabolic.orderedProductRegrouping.{uF, max uF uV} F T n d.shape
    (d.shape.adjacentMerge j h) (d.shape.adjacentRefinement j h) (d.shape.adjacentBlockEquiv j h)
    (fun _ => rfl) (d.shape.adjacent_index j h) d.blocks
  have he := funext (fun m => directFiber_induced d j h m)
  have he' := congrArg
    (fun A => (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj A) he
  obtain ⟨e⟩ := hh
  dsimp only at e
  exact ⟨e ≪≫ eqToIso he'.symm⟩

/-- The swapped refinement uses the very same outer shape. -/
theorem regroup_swapped :
    letI := T.topology
    Nonempty ((d.permute (d.shape.adjacentSwap j h)).induced ≅
      (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj
        (fun m => (swappedFiber d j h m).induced)) := by
  let := T.topology
  have hh := Parabolic.orderedProductRegrouping.{uF, max uF uV} F T n
    (d.shape.permute (d.shape.adjacentSwap j h))
    (d.shape.adjacentMerge j h) (d.shape.adjacentSwapRefinement j h)
    (d.shape.adjacentSwapBlockEquiv j h) (fun _ => rfl)
    (d.shape.adjacentSwap_index j h) (fun i => d.blocks (d.shape.adjacentSwap j h i))
  have he := funext (fun m => swappedFiber_induced d j h m)
  have he' := congrArg
    (fun A => (T.normalizedProductInductionFunctor (d.shape.adjacentMerge j h)).obj A) he
  obtain ⟨e⟩ := hh
  dsimp only at e
  exact ⟨e ≪≫ eqToIso he'.symm⟩

/-- The family of inner isomorphisms: the supplied one at the merged slot and
identities elsewhere. -/
theorem fiber_iso
    (hm₀ : letI := T.topology
      Nonempty ((mergedFiber d j h).induced ≅
        ((mergedFiber d j h).permute
          ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h))).induced))
    (m : Fin (d.shape.adjacentMerge j h).length) :
    letI := T.topology
    Nonempty ((directFiber d j h m).induced ≅ (swappedFiber d j h m).induced) := by
  let := T.topology
  by_cases hm : m.val = j
  · have he : m = d.shape.adjacentMergeIndex j h := Fin.ext hm
    subst m
    rw [swappedFiber_eq_permute]
    exact hm₀
  · rw [swappedFiber_eq_of_ne d j h m hm]
    exact ⟨Iso.refl _⟩

/-- An isomorphism between the two orders of the merged two-block datum lifts to an
isomorphism of the full products: regroup directly, map the family of fiber
isomorphisms through the outer normalized product functor, and ungroup the
swapped side. -/
theorem lift
    (hm₀ : letI := T.topology
      Nonempty ((mergedFiber d j h).induced ≅
        ((mergedFiber d j h).permute
          ((mergedFiber d j h).shape.adjacentSwap 0 (mergedFiber_swap_bound d j h))).induced)) :
    letI := T.topology
    Nonempty (d.induced ≅ (d.permute (d.shape.adjacentSwap j h)).induced) := by
  let := T.topology
  obtain ⟨e₀⟩ := regroup_direct d j h
  obtain ⟨e₁⟩ := regroup_swapped d j h
  let e : ∀ m, (directFiber d j h m).induced ≅ (swappedFiber d j h m).induced :=
    fun m => (fiber_iso d j h hm₀ m).some
  exact ⟨e₀ ≪≫ (T.normalizedProductInductionFunctor
    (d.shape.adjacentMerge j h)).mapIso (Pi.isoMk e) ≪≫ e₁.symm⟩

end AdjacentSegmentSwapLifting

end Langlands.Classification
