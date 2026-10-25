# Sum injection for two inequivalent irreducibles

`Langlands.IrreducibleSumInjectionStatement` is an internal algebraic
proposition definition. This pair states the assertion and does not prove it.

Let `k` be any field and `G` any monoid. Let `A` and `B` be irreducible
`k`-linear representations of `G`, and let `C` be any such representation.
Suppose there is no representation equivalence from `A` to `B`. For any
two nonzero intertwiners `f : A → C` and `g : B → C`, the statement asserts
that the actual intertwiner

```text
A.ρ.prod B.ρ → C.ρ,    (a, b) ↦ f(a) + g(b)
```

is injective. The Lean expression constructs this map as the sum of `f`
composed with the first product projection and `g` composed with the second
product projection. The projections, addition and composition are Mathlib's
actual `Representation.IntertwiningMap` operations. Thus the conclusion
concerns an equivariant linear map from the actual binary product, with
the displayed formula.

The coefficient field, monoid and three representation carriers have five
independent universes `uK`, `uG`, `uV`, `uW` and `uX`. Irreducibility uses
Mathlib's `Representation.IsIrreducible`: the lattice of invariant
subspaces is a nontrivial simple order. There is no finite-dimensionality,
finite-length, smoothness, admissibility or topology premise. In particular,
the ambient representation `C` need not be irreducible.

## Internal provenance and use

This assertion isolates an elementary algebraic step needed by the
supported relative recovery argument. Opposite reciprocity there gives
nonzero maps from two irreducible coarse representations into a common
opposite Jacquet representation. If those irreducibles are inequivalent,
the sum injection permits subsequent use of exactness on their binary
product.

The mathematical reason is that a nonzero map out of an irreducible is
injective, and the two simple images have zero intersection unless the
irreducibles are equivalent. Mathlib already supplies the individual
injectivity and Schur lemmas; deriving injectivity of the displayed sum
remains the exact proof-successor obligation. Disjointness of the images
is not an additional premise.

The formulation is an internal consequence of the representation and
intertwiner definitions imported here. No external source is asserted to
state this exact five-universe interface. This pair supplies neither a
joint-quotient criterion nor any Jacquet exactness, multiplicity comparison,
supported recovery or arbitrary-tempered quotient reflection theorem.
