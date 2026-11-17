# A matched-head criterion for the complex transpose pairing

This internal reduction makes the remaining classification requirement explicit. An irreducible admissible complex GK module `V` must receive a nonzero intertwiner from `X(ds)` and have a nonzero intertwiner into `X(ds.reverse)` for the very same list `ds`. The source standard module must have a largest proper GK submodule. No equality of parameter multisets is substituted for either intertwiner.

The construction `standardAdjointOfEmbedding` transposes the given embedding into the reversed standard module using the actual inverse-transpose standard duality. It gives a nonzero equivariant map `q : X(ds) → (V^vee)^theta`. Compact finiteness of the source makes the resulting functionals compact-finite. The genuine complexified real Lie action is preserved on the full tensor product.

The existing finite-dual theorem and involutive twisting make `(V^vee)^theta` irreducible. Thus both the supplied quotient map `A` and `q` have kernel equal to the largest proper GK submodule, by the published `eq_ker_of_largest_proper`. Descending `q` along the surjection `A` gives `D : V → (V^vee)^theta`. Evaluating `D(y)` on `x` is the required nonzero bilinear form, with the actual compact and differential inverse-transpose formulas.

The provenance is internal. The largest-proper-submodule premise is the per-list content of the existing `ComplexStandardLanglandsQuotientStatement`, whose original-literature correspondence is documented in `ComplexLargeStandardIrreducibleReduction.md`. This module assumes that premise and the two matched intertwiners; it proves neither their general existence nor the arbitrary-rank target. Independent work is still required to supply those inputs for every irreducible admissible module.
