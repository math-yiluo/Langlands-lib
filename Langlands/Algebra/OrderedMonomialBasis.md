# Ordered enveloping monomials along any list of basis indices

Module `Langlands.Algebra.OrderedMonomialBasis`, namespace
`Langlands.Algebra.LieWeightProjection`.

Let `L` be a Lie algebra over a field `k`, `b : Module.Basis B k L` a basis with a finite
index type, and `bs : List B` a list containing every index exactly once. The ordered
monomial `orderedMonomial k L b bs α` (module `Langlands.Representation.Archimedean.Kostant.OrderedMonomials`)
multiplies, in the order of `bs`, the powers `ι(b c)^{α c}` of the canonical generators of
the universal enveloping algebra.

- `word_expand_map`: the word of the list `expand l α` (each index `c` of `l` repeated `α c`
  times) is the product over `l` of the powers `ι(b c)^{α c}`.
- `listEquiv hbs hall : Fin bs.length ≃ B` is `List.get`, bijective because `bs` has no
  duplicates and contains every index.
- `orderedMonomial_eq_orderedPBWMonomial` identifies the ordered monomial with the
  published `orderedPBWMonomial` of the reindexed basis `b.reindex (listEquiv …).symm`
  and the exponent vector `i ↦ α (bs.get i)`. The proof expands the word of the list
  `expand bs α` into the product over `bs` of the powers and compares it with
  `List.ofFn bs.get = bs`.
- `linearIndependent_orderedMonomial_list` proves linear independence: the published
  `Langlands.Algebra.UniversalEnveloping.orderedPBWBasis` gives the independence of the
  ascending monomials of the reindexed basis, and the exponent map
  `α ↦ (i ↦ α (bs.get i))` is injective.
- `orderedMonomialBasis` is the resulting basis of `UniversalEnvelopingAlgebra k L`
  indexed by `B →₀ ℕ`. Spanning is the published
  `Langlands.Archimedean.VermaPBW.top_le_span_orderedMonomial`;
  `orderedMonomialBasis_apply` records that the basis vectors are the ordered monomials.

No characteristic assumption is made. `Langlands.Archimedean.VermaPBW.pbwBasis` needs
symbol data, which `Langlands.Archimedean.Kostant.AssocSymbol.symbolData` provides for
the commutator Lie algebra of an associative algebra; the basis here needs no such data,
so it applies to every finite basis of every Lie algebra over a field, in any order. This is an internal construction; the underlying theorem is the
Poincaré–Birkhoff–Witt theorem proved in `Langlands.Algebra.OrderedPBWBasis`.
