# Hilbert embeddings of actual automorphic tensor slices

This internal construction extends the published faithful tensor presentation
and its extracted positive forms to genuine Hilbert embeddings. Inputs remain a
number field in universe `uF`, any natural matrix rank, complex local module
carriers in independent universe `uV`, the specified representation family,
exceptional set and reference vectors with their integral-fixed law, an actual
`FiniteTensorPresentation` onto an invariant subspace `S` of automorphic forms,
and a supplied invariant positive form `b` on `S`.

The existing `separatedUnitaryForm`, `sliceUnitaryForm` and `factorUnitaryForm`
are used exactly. Restricting `b` along the actual one-place insertion copies its
positive core, so its Hilbert completion and canonical embedding are the same
as those of `b`.

`separatedHilbertEquiv` extends the actual `P.localEquiv v` to a complex-linear
isometric equivalence from the separated tensor form's completion onto the
whole `b.HilbertCompletion`. Its original-vector formula is
`j_sep(z) ↦ j_b(P.localEquiv v z)`. It retains the whole complementary tensor
space; this is not a factor identification.

`sliceHilbertEmbedding` extends the genuine subtype `sliceInclusion` to a
complex-linear isometry from the slice form's completion into that same global
completion. It sends `j_slice(f)` to `j_b(P.sliceInclusion v y f)` and works even
for the zero complementary vector and zero slice.

For an explicit nonzero complementary tensor `y` and proof `hy`,
`factorSliceHilbertEquiv` extends `P.sliceEquiv v y hy` to an isometric
equivalence from the extracted local factor form's completion onto the slice
form's completion. `factorHilbertEmbedding` composes this with the actual slice
embedding. It sends `j_factor(x)` to `j_b(P.localEquiv v (x ⊗ y))`.
All four displayed evaluation laws are implemented.

The extension constructors use the published `completedIsometry` and
`completedEquiv`. Exact form preservation follows definitionally from the
existing pullback forms. For the two equivalences, original surjectivity is
supplied by the existing actual algebraic equivalences. The factor evaluation
formula composes the embedded-vector formulas and the published exact identity
`sliceInclusion_sliceEquiv`. No positive-form preservation or Hilbert embedding
existence is assumed as new data.

Provenance is internal, by composition of published constructions from
`FiniteTensorUnitaryForm` and `Representation/Unitary/CompletionTransport`,
including its `CompletionIntertwiner` dependency. No new original-literature
identification is asserted. No existence of a positive form, genuine tensor
presentation or nonzero tail for a general automorphic representation is
claimed. The form can depend on the global choice and tail.

This unit supplies the constructors and original-vector evaluation formulas.
Explicit specializations of covariance and closed-range descriptions remain
separate work. No Hilbert tensor product decomposition, canonical local normalization, spectral occurrence,
archimedean globalization or smooth-vector recovery is asserted.
