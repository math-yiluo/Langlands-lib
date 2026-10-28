# Relative opposite-Jacquet embedding and finite-series bound

`Langlands.glRelativeJacquetEmbedding` proves exactly
`Langlands.GLRelativeJacquetEmbeddingStatement.{uF,uV,uW}`. The field, arbitrary
refined-Levi test representation and irreducible admissible coarse-Levi
representation retain independent universes. The proof adds no hypotheses.

Write `I = i_L^G(μ)` for the actual normalized upper induction and
`O = r_(op L)^G(I)` for its actual normalized opposite coarse Jacquet module.
The standard clause of `Parabolic.irreducibleOppositeJacquetUnit` supplies
an actual injective intertwiner `i : μ → O`. This published theorem uses
second adjointness on the nonzero identity of the induction and
irreducible-source injectivity.

Published normalized induction admissibility proves that `I` is admissible.
`Parabolic.isAdmissible_standardOppositeJacquet` then proves that `O` is
admissible, including smoothness. Applying
`T.normalizedRefinedOppositeJacquetMap_injective` to `i` therefore gives an
actual injection

`r_(op M)^L(μ) → r_(op M)^L(O)`.

`Parabolic.normalizedOppositeRefinementTransitivity` supplies an equivariant
equivalence from the latter iterated quotient to
`r_(op M)^G(i_L^G μ)`. Composing its forward intertwiner with the preceding
map gives the required `j : innerJacquet T B S μ → ambientJacquet T B S μ`;
the composite is injective because both factors are injective. The proof
uses the existing normalized functors and this exact opposite transitivity
equivalence, so it retains the actual radicals and half-modulus factors.

For an arbitrary test representation `τ` and a supplied actual ambient count
`M₀`, let `C` be the actual quotient of the ambient representation by the
range subrepresentation of `j`. The quotient map `q` is surjective, and
`Submodule.ker_mkQ` identifies its kernel with the range of `j`.
`jordanHolderShortExactDecomposition` applied to `j, q` and the supplied
ambient finite-series witness produces actual inner and quotient
multiplicities `m, c` with `m + c = M₀`. Natural-number arithmetic gives
`m ≤ M₀`. Thus the inner series is obtained from decomposition; it is not an
extra assumption. The argument does not require irreducibility of `τ`.

This is an internal derivation from published unit embeddings, actual
opposite Jacquet exactness and transitivity, admissibility and actual-series
decomposition. It proves the stated injection and conditional count bound.
The generic comparison, positivity criterion and irreducible-head consequence
remain separate obligations.
