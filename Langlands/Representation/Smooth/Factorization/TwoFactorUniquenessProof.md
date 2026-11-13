# Uniqueness of two external tensor factors

The theorem `Langlands.admissibleProductFactorUniqueness` proves exactly
`Langlands.AdmissibleProductFactorUniquenessStatement`, with its six independent
universe parameters. The target statement pair and its imports are unchanged.

Restrict the given equivalence of external tensor products to `G₁ × {1}`.
The second factors then have trivial action, so the published
`Langlands.TensorMultiplicity.nonempty_equiv_of_tensor_trivial` gives an
equivalence of the first irreducible factors. Its nontrivial multiplicity
hypothesis follows from irreducibility of the second source factor.
Restricting instead to `{1} × G₂`, and commuting the tensor factors with
Mathlib's `Representation.TensorProduct.comm`, gives an equivalence of the second
irreducible factors in the same way.

The cancellation lemma constructs a nonzero intertwiner by composing a tensor
slice, the supplied equivalence, and a basis coefficient. Irreducibility makes
that intertwiner bijective. Thus this proof implements the isotypic restriction
argument for uniqueness in Flath, *Decomposition of representations into tensor
products* (1979), Theorem 1, proof on printed p.180 / PDF p.176, registered
`flath-1979-tensor-products`. Renard's corresponding assertion is III.1.14,
printed p.66 / PDF p.72, registered
`renard-2026-representations-groupes-reductifs-padiques`.

This argument needs no topology or admissibility beyond the hypotheses already
present in the target. It preserves arbitrary independent carrier universes.
The only project proof dependency is the published tensor multiplicity
cancellation module; the other import supplies the unchanged target.
