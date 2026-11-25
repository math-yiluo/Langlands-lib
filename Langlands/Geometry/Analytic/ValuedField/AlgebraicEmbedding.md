# Isometric embeddings of algebraic extensions

This internal helper combines the Library's uniqueness of the extension of an
ultrametric absolute value with Mathlib's algebraic embedding theorem. Its
purpose is to extend a prescribed geometric-point character through an algebraic
extension of a completed residue field. It supplies only the field-theoretic
step; it does not assert that a particular analytic residue extension is
algebraic or construct a chart-compatible field-valued point.

Let `E`, `F` and `L` be ultrametric normed fields in independent universes.
Assume `E` is complete, `F` is a normed `E`-algebra and is algebraic over `E`.
Neither `F` nor `L` needs to be complete.

`isometry_of_norm_on_algebraic_base` proves that any ring map `φ : F →+* L`
whose restriction to `E` preserves the norm is an isometry. Pull back the norm
of `L` along `φ` and compare it with the norm of `F` using
`Langlands.Analytic.absoluteValue_eq_of_extends` from
`Langlands.Geometry.Analytic.FiniteMorphismFibres`. Both absolute values are
nonarchimedean and extend the norm on `E`. Their equality gives norm
preservation, hence preservation of distances. This argument includes the
trivially normed case because the imported uniqueness theorem includes it.

`isometry_algHom_of_isAlgebraic` applies this result to an `E`-algebra map
when `L` is also a normed `E`-algebra.

If `L` is algebraically closed, `algebraicBoundedEmbedding E F L` bundles
Mathlib's `IsAlgClosed.lift` as a `BoundedAlgHom E F L` with positive bound `1`.
`isometry_algebraicBoundedEmbedding` records that this chosen embedding is
isometric.

Finally, suppose the fields are algebras over a normed field `K` and
`K → E → F` is a scalar tower. For any prescribed isometric `K`-algebra map
`i : E →ₐ[K] L`, `exists_isometric_algebraic_extension` gives a bounded
`K`-algebra map `j : F → L` which is isometric and satisfies
`j (algebraMap E F c) = i c` for every `c : E`. Mathlib's
`IsAlgClosed.surjective_domRestrict_of_isAlgebraic` first extends `i`
algebraically. The preceding norm comparison proves this extension is
isometric and hence has bound `1`. No normed `E`-algebra structure on `L`
needs to be chosen for the prescribed-embedding version.

All results are internal deductions from published Library and Mathlib results;
no additional assertion from the literature is used.
