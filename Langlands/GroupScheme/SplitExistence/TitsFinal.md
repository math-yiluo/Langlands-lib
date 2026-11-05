# The `ℓ`-parabolic subgroup of `Γ` is `B`

Author: Worker 1398.

* `btSub`: invertible matrices block triangular for `c ↦ ℓ(wt c)` (in the order dual), i.e. the
  `K`-points of the parabolic subgroup of `GL_n` attached to the cocharacter `ℓ`. It contains
  `B` (`borelSub_le_btSub`).
* `wn_not_mem_btSub`: some weight `d` has `⟨wt d, α_i^∨⟩ > 0` (the weights generate `X`, and
  `n_i` turns a negative pairing into a positive one), and a nonzero entry `(c, d)` of `n_i` has
  `ℓ(wt c) = ℓ(wt d) − ⟨wt d, α_i^∨⟩ ℓ(α_i) < ℓ(wt d)`.
* `x_not_mem_btSub_of_neg`: for a negative root `j` and `s ≠ 0`, `x_j(s) ∉ btSub`, using that
  `e j 1` is nonzero over every field (`e_one_map_ne_zero_field`, from nonvanishing modulo every
  prime).
* `chevSub_le_sup`: every root group lies in `B ⊔ N` (Mathlib `Base.induction_reflect`).
* `isConcreteTits`: `(B, N, (n_i))` satisfies `IsConcreteTits`.
* `chevSub_inf_btSub : Γ ⊓ btSub = B`, by `IsConcreteTits.eq_of_le`.
