import Langlands.GroupScheme.OrthogonalMatrix.TypeD

/-! # Lattice automorphisms preserving the type `D` roots are signed permutations

The weights `w(x)` of the diagonal torus of `O_{2l}` are `e_a` for `x = inl a` and `-e_a` for
`x = inr a`; the roots are the differences `w(x) - w(y)` with `x` and `y` of different indices.
An injective additive endomorphism `M` of `ℤ^l` that sends every root to a root, with `l` having
at least two elements, sends every weight to a weight: `M(w(x)) = w(σ x)` for a permutation `σ`
of `l ⊕ l` commuting with `Sum.swap`.

The reason: `w(x) - w(swap y)` and `w(x) - w(y)` are roots for `y` of another index, their sum
is `2 w(x)`, and they are neither equal nor opposite. Their images under `M` are two roots, again
neither equal nor opposite, whose sum is `2 M(w(x))`; for two such roots half the sum is always a
weight (`signedRoot_half_sum`).
-/

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (weightCoord weightCoord_injective)

variable {l : Type} [DecidableEq l]

/-- The weight of `swap x` added to the weight of `x` is zero. -/
theorem weightCoord_swap_add (x : l ⊕ l) : weightCoord l x.swap + weightCoord l x = 0 := by
  rw [weightCoord_swap, neg_add_cancel]

/-- A doubled weight is never zero. -/
theorem weightCoord_add_self_ne_zero (x : l ⊕ l) : weightCoord l x + weightCoord l x ≠ 0 := by
  intro h
  have h1 := congrFun h (index x)
  rw [Pi.add_apply, weightCoord_apply_index, Pi.zero_apply] at h1
  rcases sgn_eq x with h2 | h2 <;> omega

/-- If a sum of four weights is even at the index of the first one, then the first index is the
index of the third or of the fourth weight, provided the second index differs from the first. -/
theorem index_eq_or_of_add_self {a b c d : l ⊕ l} (hab : index a ≠ index b) {v : l → ℤ}
    (hv : v + v = weightCoord l a + weightCoord l b + (weightCoord l c + weightCoord l d)) :
    index c = index a ∨ index d = index a := by
  by_contra h
  rw [not_or] at h
  have h1 := congrFun hv (index a)
  simp only [Pi.add_apply, weightCoord_apply_index, weightCoord_apply_of_ne b hab,
    weightCoord_apply_of_ne c (Ne.symm h.1), weightCoord_apply_of_ne d (Ne.symm h.2)] at h1
  rcases sgn_eq a with h2 | h2 <;> omega

/-- Half of the sum of the roots `w(a) + w(b)` and `w(c) + w(d)` when `c` has the index of `a`
and `d` has the index of `b`. -/
theorem signedRoot_half_sum_of_index_eq {a b c d : l ⊕ l} (hca : index c = index a)
    (hdb : index d = index b)
    (h1 : weightCoord l a + weightCoord l b ≠ weightCoord l c + weightCoord l d)
    (h2 : weightCoord l a + weightCoord l b + (weightCoord l c + weightCoord l d) ≠ 0)
    {v : l → ℤ}
    (hv : v + v = weightCoord l a + weightCoord l b + (weightCoord l c + weightCoord l d)) :
    ∃ z, v = weightCoord l z := by
  have half : ∀ u : l → ℤ, v + v = u + u → v = u := fun u h => by
    funext i
    have := congrFun h i
    simp only [Pi.add_apply] at this
    omega
  rcases eq_or_eq_swap_of_index_eq hca with hc | hc <;>
    rcases eq_or_eq_swap_of_index_eq hdb with hd | hd <;> rw [hc, hd] at h1 h2 hv
  · exact absurd rfl h1
  · refine ⟨a, half _ ?_⟩
    rw [hv, weightCoord_swap]
    abel
  · refine ⟨b, half _ ?_⟩
    rw [hv, weightCoord_swap]
    abel
  · refine absurd ?_ h2
    rw [weightCoord_swap, weightCoord_swap]
    abel

/-- **Half-sums of roots.** If the root `w(a) + w(b)` (with `index a ≠ index b`) and the sum
`w(c) + w(d)` are neither equal nor opposite and their sum is `2v`, then `v` is a weight. (The
parity of `2v` forces `{index c, index d} = {index a, index b}`.) -/
theorem signedRoot_half_sum {a b c d : l ⊕ l} (hab : index a ≠ index b)
    (h1 : weightCoord l a + weightCoord l b ≠ weightCoord l c + weightCoord l d)
    (h2 : weightCoord l a + weightCoord l b + (weightCoord l c + weightCoord l d) ≠ 0)
    {v : l → ℤ}
    (hv : v + v = weightCoord l a + weightCoord l b + (weightCoord l c + weightCoord l d)) :
    ∃ z, v = weightCoord l z := by
  have hv' : v + v = weightCoord l b + weightCoord l a + (weightCoord l c + weightCoord l d) := by
    rw [hv, add_comm (weightCoord l a)]
  rcases index_eq_or_of_add_self hab hv with hca | hda
  · -- `index b` is the index of `c` or `d`; it is not that of `c`.
    rcases index_eq_or_of_add_self (Ne.symm hab) hv' with hcb | hdb
    · exact absurd (hca.symm.trans hcb) hab
    · exact signedRoot_half_sum_of_index_eq hca hdb h1 h2 hv
  · rcases index_eq_or_of_add_self (Ne.symm hab) hv' with hcb | hdb
    · refine signedRoot_half_sum_of_index_eq (c := d) (d := c) hda hcb ?_ ?_ ?_
      · rwa [add_comm (weightCoord l d)]
      · rwa [add_comm (weightCoord l d)]
      · rwa [add_comm (weightCoord l d)]
    · exact absurd (hda.symm.trans hdb) hab

/-- A root `w(x) - w(y)` is the sum `w(x) + w(swap y)`. -/
theorem weightCoord_sub_eq_add (x y : l ⊕ l) :
    weightCoord l x - weightCoord l y = weightCoord l x + weightCoord l y.swap := by
  rw [weightCoord_swap, sub_eq_add_neg]

/-- **Images of weights.** An injective additive endomorphism of `ℤ^l` sending roots to roots
sends each weight to a weight, provided `l` has at least two elements. -/
theorem exists_map_weightCoord_eq [Nontrivial l] (M : (l → ℤ) →+ (l → ℤ))
    (hM : Function.Injective M)
    (hroot : ∀ x y : l ⊕ l, index x ≠ index y →
      ∃ x' y' : l ⊕ l, index x' ≠ index y' ∧
        M (weightCoord l x - weightCoord l y) = weightCoord l x' - weightCoord l y')
    (x : l ⊕ l) : ∃ z, M (weightCoord l x) = weightCoord l z := by
  obtain ⟨a, ha⟩ := exists_ne (index x)
  set y : l ⊕ l := Sum.inl a
  have hy : index x ≠ index y := Ne.symm ha
  have hy' : index x ≠ index y.swap := by rwa [index_swap]
  obtain ⟨p, q, hpq, hr⟩ := hroot x y.swap hy'
  obtain ⟨p', q', -, hs⟩ := hroot x y hy
  replace hr := hr.trans (weightCoord_sub_eq_add p q)
  replace hs := hs.trans (weightCoord_sub_eq_add p' q')
  have hsum : M (weightCoord l x - weightCoord l y.swap) + M (weightCoord l x - weightCoord l y) =
      M (weightCoord l x) + M (weightCoord l x) := by
    rw [← map_add M, ← map_add M, weightCoord_swap]
    congr 1
    abel
  refine signedRoot_half_sum (a := p) (b := q.swap) (c := p') (d := q'.swap)
    (by rwa [index_swap]) ?_ ?_ ?_
  · rw [← hr, ← hs]
    intro h
    have h' := sub_eq_zero.mpr (hM h)
    rw [sub_sub_sub_cancel_left, sub_eq_zero] at h'
    exact swap_ne_self y (weightCoord_injective h'.symm)
  · rw [← hr, ← hs, hsum, ← map_add M]
    exact fun h => weightCoord_add_self_ne_zero x (hM (h.trans (map_zero M).symm))
  · rw [← hr, ← hs, hsum]

/-- **Signed permutations.** An injective additive endomorphism of `ℤ^l` sending roots to roots
acts on the weights by a permutation `σ` of `l ⊕ l` commuting with `Sum.swap`, provided `l` has
at least two elements. -/
theorem exists_perm_map_weightCoord [Finite l] [Nontrivial l] (M : (l → ℤ) →+ (l → ℤ))
    (hM : Function.Injective M)
    (hroot : ∀ x y : l ⊕ l, index x ≠ index y →
      ∃ x' y' : l ⊕ l, index x' ≠ index y' ∧
        M (weightCoord l x - weightCoord l y) = weightCoord l x' - weightCoord l y') :
    ∃ σ : Equiv.Perm (l ⊕ l), (∀ x, σ x.swap = (σ x).swap) ∧
      ∀ x, M (weightCoord l x) = weightCoord l (σ x) := by
  choose f hf using exists_map_weightCoord_eq M hM hroot
  have hinj : Function.Injective f := fun x y h =>
    weightCoord_injective (hM (by rw [hf, hf, h]))
  refine ⟨Equiv.ofBijective f hinj.bijective_of_finite, fun x => ?_, hf⟩
  apply weightCoord_injective
  rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, ← hf, weightCoord_swap, map_neg, hf,
    weightCoord_swap]

end Langlands.GroupScheme.OrthogonalMatrix
