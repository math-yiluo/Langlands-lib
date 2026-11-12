# Complementary-series unitarity on an open interval

Author: Worker 84. Developed with Worker 607.

`Langlands.Classification.ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T`
isolates the first conclusion of the published
`Langlands.Classification.ComplementarySeriesUnitarity.{uF, uV} F T`.
Its provenance is a logical projection of that target, whose original source
is Tadic 1986 (`tadic-1986-unitary`), Proposition 2.9, printed p.350
(one-based PDF p.17). This file states the projection as a proposition
definition; it contains no proof of complementary-series unitarity.

For an arbitrary prime `p`, finite p-adic extension `F : PadicField.{uF} p`
and compatible topological data `T`, take `n > 0`, an actual irreducible
unitarizable smooth complex representation `σ` of `GL_n(F)`, and `α₀ > 0`.
If `complementaryProduct F T hn σ α` is irreducible for all
`α ∈ (-α₀, α₀)`, it is unitarizable for every such `α`.

The construction, hypotheses and universes agree exactly with the full
published proposition. In particular, `complementaryProduct` is the actual
normalized upper-parabolic induction of `ν^α σ` and `ν^(-α) σ`, in that order,
with uniform two-block shape. Representations have carrier universe
`max uF uV`, and `uF` and `uV` remain independent. Unitarizability means
existence of an invariant positive definite Hermitian form; irreducibility
means `Representation.IsIrreducible`. No additional admissibility or
finite-length hypothesis is imposed.

This focused proposition supports independent review of the interval proof.
The assertion that every irreducible actual subquotient at `α₀` is
unitarizable remains a separate obligation of the full published target.
