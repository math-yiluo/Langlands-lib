# Original scalar coordinates on permuted cuspidal tensors

This internal proposition concerns an analytically square-integrable actual
representation, an ordered block shape, and actual supercuspidal factors on
its blocks. For every original factor it fixes a scalar character `c i` and
a real coordinate `x i` satisfying the original scalar-action equation and
the norm formula `‖c i a‖ = |a|^(x i)`.

For any permutation `e` mapping new positions to original factor labels,
suppose the actual external tensor of `C (e i)` occurs as a subquotient of
the normalized upper Jacquet module for `B.permute e`. The proposition
concludes that the exact vector `x ∘ e` has total zero and strictly positive
proper prefix sums. Field and representation carrier universes are independent.

The intended internal derivation uses the original characters `c (e i)` on
the permuted factors. Their product acts on the actual tensor, and its norm
is the product with exponents `x (e i)`. The tensor is nonzero because every
supercuspidal factor is irreducible and nonzero. The actual scalar-subquotient
cone theorem then gives the asserted cone. No new existential choices of
characters or unitarizing exponents are needed.

In the intended application, `x i = -((B.size i : ℝ) * t i)`. Permuting
the entire coordinate retains every individual rank and every repeated
factor label. The assertion does not assume equal ranks.

This file states the adapter; it supplies no proof, constructs no permutation
or actual Jacquet occurrence, and asserts no common integral cuspidal line.
Those constructions remain separate obligations in the host existence task.
