# Moving a field point of a dynamic parabolic quotient into the opposite cell

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. That proof
translates the given points by an element `g ∈ G(k)` so that they land in the
open cell. This module proves the algebraic form of the "suitable `g`"
condition. Density of `G(k)` is not used here; it enters later, through an
algebraic statement about `k`-points avoiding a hypersurface. The result is
derived from the Library's `FlagQuotientAction` and from this task's helper
modules `OppositeCellPoints` and `FieldPointBasicOpen`; it is not quoted from
the source.

Setting: `k` is a field and `G = Spec B` a corepresented affine group with
`Smooth`, `IsAffineHom` and `IsAffine` instances. `χ` is a cocharacter, and
`q : G ⟶ Q` is flat, surjective and quasi-compact with fibers the right cosets
of `P_G(χ)` (`hf`). `K` is a field extension of `k` and `x : Spec K ⟶ Q`.

## `exists_ne_zero_eq_mul_comp`

There is a nonzero `f ∈ K ⊗[k] B` such that every `k`-point `a : B → k` with
`evalMap K a f ≠ 0` satisfies `x = (a_K * u) ≫ q` for some
`u ∈ U_G(χ⁻¹)(K)`. Here `a_K = ofAlgHom ((Algebra.ofId k K) ∘ a)` is `a` viewed
as a `K`-point.

Proof as implemented. On `T = Spec (K ⊗[k] B)` use the tautological point
`g₀ = ofAlgHom includeRight` of `G` and the projection
`p₀ : T → Spec K` (given by `includeLeft`). Let `y = g₀⁻¹ · (p₀ ≫ x)`, where `·` is the Library's action
`flagQuotientAct` of `G` on `Q`. Let `O ⊆ T` be the preimage under `y` of the
opposite cell; it is open (`isOpen_cell`).

- `O` is nonempty. By `exists_lift_of_surjective` there are a field `K'`,
  `β : K → K'` and `γ ∈ G(K')` with `x ∘ Spec β = q ∘ γ`. The map
  `K ⊗ B → K'` built from `β` and the classifying map of `γ` gives a
  `K'`-point of `T`. Its composite
  with `y` is `γ⁻¹ · (γ ≫ q) = 1 ≫ q`, by naturality of the action and
  `flagQuotientAct_lift`. This lies in the cell (`range_one_subset_cell`).
- `exists_ne_zero_range_subset` gives `f`. For `a` with `evalMap K a f ≠ 0`
  (applied with `φ = evalMap K a`),
  the point `Spec (evalMap K a)` of `T` lies in `O`. Its composites with `g₀`
  and `p₀` are `a_K` and the identity, so its composite with `y` is
  `a_K⁻¹ · x`. That point lands in the cell, so `exists_mem_unipotent` gives
  `u ∈ U_G(χ⁻¹)(K)` with `u ≫ q = a_K⁻¹ · x`. Then
  `x = a_K · (u ≫ q) = (a_K * u) ≫ q`, by `flagQuotientAct_inv_cancel` and
  `flagQuotientAct_lift`.
