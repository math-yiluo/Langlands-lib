# A binomial Leibniz bound for complete ordered derivative families

This internal statement by Worker 94 concerns the actual real Fréchet
derivatives of a continuous bilinear product. It is a finite-family version of
the ordinary binomial Leibniz bound, with the Euclidean norm of the complete
ordered derivative array replacing the operator norm of a multilinear map.
No external theorem is transcribed.

`OrderedDerivativeFamilyLeibnizStatement v B` states that two finite families
`f` and `g`, smooth on an open set `S`, satisfy at every `x ∈ S` and every order
`p` the inequality

```text
T_p((i,j) ↦ B(f_i,g_j))
  ≤ ‖B‖ ∑_{l=0}^p choose(p,l) T_l(f) T_{p-l}(g).
```

Here `T` is exactly `orderedDerivativeFamilyNorm` in the named direction
family `v`. The bilinear map is real continuous bilinear; complex
multiplication is one specialization. The directions and finite family types
have arbitrary universes and may be empty. Orders include zero. No
orthogonality, unit-vector assumption, positive dimension or completeness
hypothesis is imposed.

The factor is exactly the operator norm of `B`. There is no further constant
depending on the number of directions or on the derivative order. The intended
proof differentiates once, applies the finite-family triangle inequality to the
two product terms, uses exact first-derivative family nesting, and combines the
two sums by Pascal's binomial identity. At order zero, the squared finite sums
factor over the two independent family indices.

For canonical Euclidean directions and singleton complex families, this gives
the binomial product estimate for the actual complete ordered derivative
tensors used in scalar elliptic estimates. Combining a coefficient's
operator-norm derivative bound with its own tensor norm may introduce a
dimension factor depending on that coefficient derivative order. This
statement introduces no factor depending on the total differentiated order.
Coefficient bounds, variable-operator commutators, weighted recurrences,
analyticity and automorphic growth remain separate obligations.
