# Cardinalities of kernels in finite groups

This module proves two counting lemmas. It defines nothing. All names are in the namespace `Langlands.Algebra.PadicLattice`.

## Results

- `card_ker_eq_card_quotient_range`: for an endomorphism `f` of a finite additive group `L`, `#ker f = #(L ⧸ range f)`. Lagrange's theorem gives `#L = #(L ⧸ range f) · #range f`, and the first isomorphism theorem gives `#L = #range f · #ker f`. Then cancel `#range f > 0`.
- `norm_card_eq_norm_card_ker_pow`: let `K` be a finite commutative group with `#K ≤ N`. Then the `p`-adic norm of `#K` equals the `p`-adic norm of the number of elements of `K` killed by `p ^ N`. Indeed `#K = #ker · #range` for `x ↦ x ^ (p ^ N)`, and `p` does not divide `#range`. Suppose it did. Cauchy's theorem (`exists_prime_orderOf_dvd_card'`) gives `y = x ^ (p ^ N)` of order `p`. Write `orderOf x = p ^ a · c` with `p ∤ c`. Since `p ^ a ≤ orderOf x ≤ #K ≤ N`, we have `a ≤ N`, so `y ^ c = 1` and `p ∣ c`, a contradiction. Finally `‖#range‖ = 1` by `Padic.norm_natCast_eq_one_iff`.

## Provenance

Standard finite group theory. These lemmas carry out the steps `|#Ker β|_l = (#Ker(β)(l))^{-1}` and the comparison of a kernel with a cokernel in Milne, *Abelian Varieties* (author revision 2022), proof of Proposition 12.9, p. 23.
