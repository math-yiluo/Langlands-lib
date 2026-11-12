# Quasi-affine representations under restriction of scalars

Author: Worker 110.

This is derived construction infrastructure for the relation and equalizer
steps in Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Lemma 5.10, printed pp.17–18.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad uses Zariski's Main Theorem to make the atlas relation
quasi-affine and hence quasi-projective, restricts that scheme, and
identifies the resulting functor as the kernel pair of the restricted
atlas. This module supplies scheme representation, its properties and
the preservation of pullback squares; it does not supply the
restricted atlas's étaleness or surjectivity.

`weilRestriction_presheaf_isPullback` states that precomposition with
scheme base change preserves a pullback square of full presheaves.
The proof evaluates the original square at the base-changed test
scheme and then uses the pointwise pullback criterion. Its schemes,
base morphism and presheaves are arbitrary: no finite hypothesis is
needed for this categorical fact.

For the remaining declarations, `R'` is an arbitrary finite projective
algebra over an arbitrary commutative ring `R`. The actual scheme `Y`
over `Spec R'` is locally of finite type and quasi-affine.
Mathlib's quasi-affine predicate includes quasi-compactness and implies
absolute separatedness; it therefore also supplies relative
separatedness over `Spec R'`.

`hasFiniteAffineNeighborhoods_of_quasiAffine` applies the published
finite-set affine neighborhood theorem for quasi-affine schemes.
It constructs the exact affine-open neighborhood used by
`HasFiniteAffineNeighborhoods`, including for the empty finite set.
`quasiAffineWeilRestrictionPresheafIso` then specializes the published
finite-affine-neighborhood comparison to this proved input. The
forward map is the existing glued counit comparison, recorded by
reflexivity in its component lemma.

`quasiAffineWeilRestriction_schemeProperties` obtains local finite type,
quasi-compactness and relative separatedness of the existing glued
Weil scheme. Local finite type and separatedness use its published
instances; quasi-compactness uses the finite affine cover theorem
with the proved finite-set affine neighborhoods.

`quasiAffineWeilRestriction_isAlgebraicSpace` transports the represented
scheme's algebraic-space property through the full presheaf isomorphism.
For any witness of that property, the remaining theorems give
`FiniteTypeOverRing R`, separatedness and quasi-separatedness of the
resulting restricted space. Finite type transfers its representing
scheme's identity atlas. The two diagonal properties transfer the
represented scheme diagonal using `relative_diag_schemeYoneda`
and `relative_diag_of_iso`.

This proves the displayed representability and geometric claims
without a supplied projective immersion, Noetherianity, field
hypotheses or finite freeness. It does not claim that the resulting
scheme is quasi-affine or quasi-projective. It does not prove
restriction of general algebraic spaces, finite-presentation
preservation for a general quasi-affine source, or geometric
properties of maps between restrictions.
