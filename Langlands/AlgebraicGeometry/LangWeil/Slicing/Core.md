# The slicing estimate for an affine family over an integral base

Author: Worker 5132.

This module proves the ring-level core of the hyperplane-slicing step
`FamilyLangWeilSlicingStatement`. It uses the other helper modules in `Slicing/`.

## Main result

`affineFamilyLangWeil_slicing hB hUB d hLW` assumes:

- Bertini's theorem for the generic hyperplane section (`BertiniGenericHyperplaneStatement`);
- the uniform point-count upper bound (`FamilyPointUpperBoundStatement`);
- the uniform Lang–Weil estimate in fibre dimension `d + 1` (`FamilyLangWeilInDimension (d + 1)`).

Let `R` be a domain of finite type over `ℤ`, `A` an `R`-algebra of finite type and `r₀ ≠ 0` in
`R`. Suppose that for every field `K` over `R` in which `r₀` does not vanish, `K ⊗[R] A` has
prime nilradical and Krull dimension `d + 2`. Then there are `r ≠ 0` in `R` and `C > 0` with

`|#(A →ₐ[R] κ) - (#κ)^(d+2)| ≤ C (#κ)^(d + 2 - 1/2)`

for every finite field `κ` over `R` in which `r` does not vanish. All types are in universe `u`.

This is the affine form of the slicing step: a geometrically irreducible affine family of
dimension `d + 2` over an integral base, restricted to a dense open subset of the base. The
reduction from arbitrary families to this case is a separate module.

## Provenance

Provenance: internal. The mathematical route is the induction step of Lang and Weil, *Number of
points of varieties in finite fields* (Amer. J. Math. 76 (1954), registered source
`lang-weil-1954-number-of-points`, printed pp. 822–823), and of Tao, *The Lang–Weil bound*
(registered source `tao-2012-lang-weil-bound`, Section 2). Count pairs (point, hyperplane
through it). Apply the estimate in dimension `d + 1` to good hyperplane sections. Bound the
exceptional hyperplanes and their points crudely. The uniformity of the exceptional set comes
from applying the family statements over the parameter ring of hyperplanes, as described in the
Markdown of `FamilyLangWeilSlicingStatement`.

## Proof

Write `g : Fin m → A` for generators of `A` (from `Algebra.FiniteType.iff_quotient_mvPolynomial''`)
and `𝒫 = R[a_*, a_0, …, a_{m-1}]` for the parameter ring of affine hyperplanes. The main work is
in `abs_natCard_sub_le_of_slicing`.

1. **Bad parameters.**
   - `c₁`: Bertini plus spreading (`exists_ne_zero_forall_nilradical_slice_isPrime`, applied
     because the generic fibre is geometrically irreducible of dimension `d + 2 ≥ 2`). If
     `c₁(β) ≠ 0`, the hyperplane section `Slice R g β` has prime nilradical.
   - `c₂`: Chevalley (`exists_ne_zero_forall_hyp_not_mem_nilradical`, applied to a point of `A`
     in a field containing `R`, from `exists_field_algHom`). If `c₂(β) ≠ 0`, the hyperplane does
     not contain the fibre.

   Let `c = r₀ c₁ c₂`. By `slice_isPrime_and_dim` and the dimension lemmas
   (`ringKrullDim_quotient_span_singleton_eq`), `c(β) ≠ 0` implies that `Slice R g β` has prime
   nilradical and dimension `d + 1`.
2. **Lang–Weil for good slices.** `exists_langWeil_away` applies
   `FamilyLangWeilInDimension (d + 1)`, through `langWeil_ring_of_forall` and
   `exists_langWeil_slice`, to the universal hyperplane section over `𝒫[1/c]`. Every field
   point of `𝒫[1/c]` has `c ≠ 0` (`aeval_algebraMap_ne_zero`), so its fibres are hyperplane
   sections `Slice R g β` with `c(β) ≠ 0` (`tensor_slice_isPrime_and_dim`). This gives one
   constant `C₁`. For `α ∈ κ^{m+1}` with `c(α) ≠ 0`, the points of `A` on the hyperplane `α`
   are the `κ`-points of this family over the point `𝒫[1/c] → κ` given by `α`
   (`abs_card_filter_sub_le_of_away`, `natCard_slice_algHom`).
3. **Upper bound for the other slices.** `exists_upperBound_slice` applies
   `FamilyPointUpperBoundStatement` to the universal hyperplane section over `𝒫` and gives a
   constant `C₂`. If the hyperplane `α` does not contain the fibre, the residue-field fibre at
   `ker (𝒫 → κ)` has dimension at most `d + 1` (`ringKrullDim_tensor_slice_le`), so at most
   `C₂ (#κ)^(d+1)` points lie on it (`natCard_slice_le_of_upperBound`,
   `card_filter_le_of_upperBound`).
4. **Counting over one finite field** (`abs_card_sub_le_of_slices`). Take `κ` with `r₀` and
   the coefficient `c_{m₀}` of `c` nonzero in `κ` (so `r = r₀ c_{m₀}`), and let
   `Λ = {α : linear part ≠ 0}`, of size `q (q^m - 1)` with `q = #κ`
   (`card_filter_linear_ne_zero`).
   - The double count `sum_card_filter_hyperplane` gives
     `∑_{α ∈ Λ} #{x on α} = #(A →ₐ[R] κ) · (q^m - 1)`.
   - `Λc`: the hyperplanes containing the fibre, those with `hyp R g α` nilpotent in
     `κ ⊗[R] A`. They contain every point. Some generator is not congruent to a constant
     modulo the nilradical (`exists_forall_sub_algebraMap_not_mem_nilradical`, since the
     dimension `d + 2` is positive), so `card_filter_mem_ideal_mul_le` gives
     `(#Λc + 1) q ≤ q^m`.
   - `Λb`: hyperplanes not containing the fibre with `c(α) = 0`. Since `c` stays nonzero over
     `κ`, Schwartz–Zippel gives `#Λb ≤ deg(c) q^m`. Each such slice has at most
     `C₂ q^(d+1)` points.
   - Every other `α ∈ Λ` has `c(α) ≠ 0` and satisfies step 2.

   `abs_sub_pow_le_of_slices` then gives the estimate with constant
   `C = 2 (2 + deg c + C₁ + deg c · C₂)` (`abs_natCard_sub_le_of_constants`).

## Other declarations

- `card_filter_linear_ne_zero`, `totalDegree_map_le`, `finite_algHom_of_adjoin`,
  `exists_forall_sub_algebraMap_not_mem_nilradical`, `hyp_eq_algebraMap_add_sum_smul` and
  `finiteType_int_of_finiteType` are small auxiliary facts used above. The last gives
  finite type over `ℤ` through the instance `Ring.toIntAlgebra` expected by `Bridges.lean`.
- `exists_field_algHom`: if `Frac R ⊗[R] A ≠ 0`, then `A` has a point in a field into which `R`
  injects (a residue field of `Frac R ⊗[R] A`).
