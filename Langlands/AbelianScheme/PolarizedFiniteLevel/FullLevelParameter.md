# The full-level parameter scheme in a supplied family

Let `A` be a supplied abelian scheme over `S`, and let `g,n` be natural
numbers. For positive `n` invertible in the global sections of `S`,
`fullLevelParameterScheme A g n hn hunit` is an actual scheme over `S`.
It is the full-level open subscheme of `torsionTupleScheme A g n`,
defined by the unchanged full-level condition on the tautological
ordered tuple. The unit hypothesis on the tuple scheme follows by
pullback from `S`.

For every actual `T : Over S`, `fullLevelParameterHomEquiv` gives an
equivalence between morphisms from `T` to this parameter scheme over `S`
and `FullLevel ((baseChange T.hom).obj A) g n`. This is the existing
ordered-tuple definition with its basis condition at every
algebraically closed field-valued point. There is no restriction on the
test scheme or its structure map, and no noetherianity, dimension or
numerical torsion-rank assumption.

The main compatibility step identifies the prescribed coordinates,
rather than only the abstract fibre modules. At a field-valued point
`s` of a test scheme, restriction commutes with the actual
`sectionTupleBaseChangeEquiv`. For a morphism from that test scheme to
the tuple parameter, `torsionTupleFibreComparison` composes the two
actual torsion base-change linear equivalences, the test-scheme
isomorphism supplied by its structure equation, and the inverse direct
base-change equivalence. `torsionTupleFibreComparison_apply` proves
that this comparison sends every pulled-back tautological coordinate
to the corresponding decoded coordinate. It uses restriction
compatibility, the tautological projection formula, and equality of
the underlying actual kernel-section morphisms. Transporting the
specified bases through this linear equivalence in both directions
proves `isFull_torsionTupleSectionEquiv_iff`.

The published universal property of the full-level locus then gives a
unique lift precisely for maps whose decoded tuple is full.
`fullLevelParameterHomTupleEquiv` records this factorization in
`Over S`; the structure equation follows from the locus factorization
and the original structure equation. Monomorphism cancellation and
the factorization equation prove its inverse laws. Composing with the
tuple classification and retaining the fullness proof gives
`fullLevelParameterHomEquiv`.

The section formula is exact. After the canonical comparison with the
original actual torsion modules, `fullLevelParameterHomEquiv_comp`
proves that classification commutes coordinatewise with every
actual map of test schemes over `S`. It follows from precomposition
naturality of `torsionTupleHomEquiv`. Decoding the identity morphism
gives `fullLevelParameterUniversalLevel`, a full level on the actual
pullback of `A` to this parameter scheme.

The provenance is internal: this construction combines the existing
actual tuple parameter, torsion base-change comparisons, prescribed
geometric-fibre bases and full-level locus universal property. It
parameterizes full levels in one supplied family. It does not assert
nonemptiness, finite or etale structure maps, automorphism rigidity,
or existence of an ambient moduli space.
