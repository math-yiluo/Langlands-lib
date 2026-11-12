# Alternation of the actual finite pairing of a relative polarization

`Langlands.AbelianScheme.relativeFiniteWeilAlternation` proves exactly
`Langlands.AbelianScheme.RelativeFiniteWeilAlternationStatement`.
The theorem applies the published
`relativeFiniteWeilAlternation_of_multiplicationIsogeny` to the published
unconditional theorem `Langlands.GroupScheme.multiplicationIsogeny`.
There is no remaining multiplication-isogeny premise.

The target retains all nine tensor/Picard constructor propositions, the
quasi-separated base `S`, the actual abelian scheme `A/S`, the chosen
dual-constructor inputs, dual geometry, inverse Poincare line bundle and
evaluation, and the actual dual-valued homomorphism `lam` satisfying exactly
`IsPolarization`. For each positive natural number `n`, the conclusion is
the equation in `Over S`

```text
diagonal_A[n] ; finiteWeilAlongHomPairing(lam,n) = 1 : A[n] -> mu S n.
```

Here `A[n]` is the actual multiplication kernel and `1` is the constant
identity-section morphism. The pairing remains the Poincare-derived
evaluation `beta(lam[n](y))(x)`, in that order.

The imported reduction proves this morphism equation by the following
implemented argument. The published diagonal Poincare normalization
presents `2 • lam` by a global Mumford bundle. Mumford alternation and
additivity of evaluation in `lam` imply that the universal diagonal value
at level `2*n` has square one. The actual torsion transition
`A[2*n] -> A[n]` and its pairing compatibility identify the level `n`
diagonal value, after inclusion in `Gm`, with that square. The transition
is a pullback of multiplication by `2`. The unconditional
`multiplicationIsogeny` makes multiplication by `2` flat and surjective,
so the transition is an epimorphism. Cancelling this epimorphism and the
monic inclusion `mu S n -> Gm` gives the stated equation.

Thus the conclusion is an equality of actual scheme morphisms and applies
to nonreduced test schemes. The proof adds no invertibility,
principal-polarization or characteristic restriction, including in
characteristic two.

This is an internal composition of published Library proofs. Its proof
route and constructor conventions are documented in
[FiniteWeilAlternationReduction.md](FiniteWeilAlternationReduction.md),
and the unconditional multiplication theorem is explained in
[MultiplicationIsogenyProof.md](../../AbelianScheme/MultiplicationIsogenyProof.md).
The target and every imported Lean/Markdown pair are unchanged.
