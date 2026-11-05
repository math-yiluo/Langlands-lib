# Smooth connected solvable groups as semidirect products with a maximal torus

Worker 950, using the conditional reduction of Worker 1496.

`Langlands.GroupScheme.solvableMaximalTorusSemidirect` proves the published
proposition `Langlands.GroupScheme.SolvableMaximalTorusSemidirectStatement.{u}`
for an arbitrary universe `u`, with no additional premise.

Let `k : Type u` be an algebraically closed field, `H` a smooth connected
solvable affine group scheme over `Spec k`, and `s : T ⟶ H` a maximal torus.
The conclusion is a closed subgroup `u : U ⟶ H`, with `U` smooth, connected
and unipotent, whose range is normal in `H` on every test scheme and contains
the range of every unipotent closed subgroup of `H`. Moreover, the
multiplication morphism `subgroupMultiplication u s : U × T ⟶ H` is an
isomorphism. The exact encoding is described in
[the target statement](SolvableMaximalTorusSemidirectStatement.md).

## Implemented proof

The proof is one application of the published theorem
`solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient` from
[`TriangularTorusConjugacy`](TriangularTorusConjugacy.md). It has type

```text
SolvableTorusQuotientStatement.{u} → SolvableSplitExtensionStatement.{u} →
SolvableMaximalTorusSemidirectStatement.{u}
```

and its two premises are supplied by published proofs at the same universe:

- `solvableTorusQuotient : SolvableTorusQuotientStatement.{u}`, in
  [`SolvableTorusQuotientProof`](SolvableTorusQuotientProof.md). It gives the
  smooth connected unipotent normal subgroup `i : U ⟶ H` and a represented
  fppf quotient `q : H ⟶ D` by its range onto a split torus.
- `solvableSplitExtension : SolvableSplitExtensionStatement.{u}`, in
  [`SolvableSplitExtensionProof`](SolvableSplitExtensionProof.md). It gives a
  homomorphic section `σ : D ⟶ H` of `q`.

Inside the reduction, `s ≫ q` is an isomorphism for every maximal torus `s`,
by torus conjugacy in the triangular group. The multiplication map is then an
isomorphism, and every unipotent closed subgroup lies in the range of `i`.
The details are in the Markdown of `TriangularTorusConjugacy`.

The axioms are `propext`, `Classical.choice` and `Quot.sound`. The proof
does not use `MaximalTorusConjugacyStatement`,
`SolvableMaximalTorusConjugacyStatement` or
`MaximalRankRadicalTorusIntersectionStatement`.

## Provenance and scope

The target is the first clause of Milne, *Algebraic Groups* (2017),
Theorem 16.33(d), printed pp.335–336, registered source
`milne-2017-algebraic-groups`: for `k` algebraically closed and `T` a maximal
torus of a smooth connected solvable group `G`, `G = G_u ⋊ T`. The
implemented route is the Library's triangular reduction described above, not
Milne's proof. This module only combines published results; the target pair
and all its imports are unchanged.
