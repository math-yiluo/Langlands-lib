# Canonical reduced norm in arbitrary finite matrix charts

This module extends the published reduced-norm comparison from matrix
indices `Fin (reducedDegree K A)` to any finite type of matrix indices.
Let `K` be a field and `A` a finite-dimensional central simple `K`-algebra,
in an arbitrary common universe. For any field extension `L/K` and actual
chart `e : L ⊗[K] A ≃ₐ[L] Matrix I I L`, the theorem
`card_eq_reducedDegree` identifies the cardinality of `I` with the
canonical reduced degree.
`canonicalSizeChart` constructs the actual chart reindexed to that size.
These dimension and reindexing constructions themselves require only a
supplied chart, without centrality, simplicity or finite dimensionality.

`reducedNorm_eq_det_fintype` proves that the actual canonical
`reducedNorm K A R` is the determinant of `splittingMap e R` on every
commutative `L`-algebra `R`, with compatible `K` structure. No finiteness,
Galois or separability assumption is imposed on this splitting field.
The splitting field, matrix indices and test algebra have independent
universes. No reducedness or nontriviality assumption is imposed on the
test algebra. The direct-field specialization is
`reducedNorm_eq_chart_det_fintype`.

The proof reindexes the chart first by a finite enumeration and then by
the proved cardinality equality. It applies the published canonical
comparison to the resulting chart of canonical size. The extended chart
maps commute with this simultaneous row and column reindexing, by their
pure-tensor formula and tensor induction. Determinant is unchanged by
that reindexing. Thus no mathematical choice of norm is added.

For a finite Galois splitting field, nonempty finite matrix indices,
and any finite coordinate basis `b`, `normFromGalois_eq_reducedNorm`
identifies the existing chart-descended determinant law with the
canonical reduced norm on every commutative `K`-algebra. The proof
extends scalars faithfully to `L ⊗[K] R`, uses naturality of both actual
laws and their determinant comparisons there, and reflects the equality
through the injective scalar inclusion. It does not infer a polynomial
identity from equality on field-valued points.

`normFromGaloisUnits_eq_reducedNormUnits` identifies the actual
homomorphisms on units. Taking their literal kernels proves
`normFromGaloisOne_eq_reducedNormOne`. These are equalities of the
existing constructions, rather than new substitute definitions.

This is an internal derivation from `ReducedNorm`, its imported
all-test comparison, and Mathlib's matrix reindexing results. It adds no
external-source assertion. It supplies no local arithmetic,
coefficient commutator-kernel theorem, group-scheme representability or
proof of `LocalKneserTitsStatement`.
