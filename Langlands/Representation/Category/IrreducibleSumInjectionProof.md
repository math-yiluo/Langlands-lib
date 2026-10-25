# Sum injection for two inequivalent irreducibles

`Langlands.irreducibleSumInjection` proves the proposition
`Langlands.IrreducibleSumInjectionStatement` from
`Langlands.Representation.Category.IrreducibleSumInjectionStatement`.

For any field `k` and monoid `G`, let `A` and `B` be irreducible
representations and `C` an arbitrary representation of `G` over `k`.
If `A` and `B` have no representation equivalence and
`f : A → C`, `g : B → C` are nonzero intertwiners, the theorem proves
injectivity of

```text
A.ρ.prod B.ρ → C.ρ,    (a, b) ↦ f(a) + g(b).
```

The actual map is the sum of `f` composed with the first product projection
and `g` composed with the second. Both summands are actual intertwiners,
so their sum already has equivariance and linearity. No replacement
carrier, chosen abstract direct sum or quotient is used in the conclusion.

The field, monoid and three representation carriers retain the five
independent universes `uK`, `uG`, `uV`, `uW` and `uX`. There is no
finite-dimensionality, finite-length, smoothness, admissibility or
topology assumption. In particular, `C` need not be irreducible.

## Implemented argument

Since `B` is irreducible, Mathlib's
`Representation.IsIrreducible.injective_or_eq_zero` makes `g` injective.
Define the actual subrepresentation `K` of `A` to have underlying submodule
the preimage of `range(g)` under `f`. Its invariance follows from the
intertwining identity for `f` and invariance of `range(g)`.
Irreducibility of `A` gives `K = ⊥` or `K = ⊤`.

In the full case, every `f(a)` lies in `range(g)`. The proof uses
`LinearEquiv.ofInjective g.toLinearMap` to invert `g` on its range and
composes that inverse with the range-restricted linear map `f`.
This constructs a linear map `l : A → B` with `g(l(a)) = f(a)`.
Applying injectivity of `g` and both original intertwining identities
proves equivariance of `l`, giving an intertwiner `q : A → B`.

The intertwiner `q` is nonzero: if it were zero, the identity
`g(l(a)) = f(a)` would make `f` zero. Both its source and target are
irreducible, so Mathlib's
`Representation.IsIrreducible.bijective_or_eq_zero` makes it bijective.
`q.ofBijective` then gives a representation equivalence `A ≃ B`,
contrary to the hypothesis. This rules out the full case and proves
`K = ⊥`.

Finally, consider an actual pair `(a,b)` in the kernel of the sum map.
The equation `f(a) + g(b) = 0` gives `f(a) = g(-b)`, so `a ∈ K`.
Thus `a = 0`. The same kernel equation then gives `g(b) = 0`,
and injectivity of `g` yields `b = 0`. The kernel is zero, so
`LinearMap.ker_eq_bot` proves injectivity of the displayed intertwiner.

## Internal provenance and scope

This is an internal algebraic derivation on the actual Mathlib
representation and intertwiner constructions. The proof uses the
invariant-subspace definition of irreducibility and Mathlib's Schur lemmas;
no external literature is asserted to give this exact five-universe
interface. The proof takes no disjoint-image certificate as a premise:
the invariant preimage argument supplies the needed separation.

The supported relative recovery proof can apply this theorem after
opposite reciprocity has produced the two nonzero embeddings into one
opposite Jacquet module. This pair does not supply that reciprocity,
Jacquet exactness, multiplicity comparisons, supported recovery or
arbitrary-tempered quotient reflection. Those remain separate obligations.
