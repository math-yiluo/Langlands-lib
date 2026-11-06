# Serre classes defined by actual irreducible subquotients

This internal construction applies to smooth representations over any field,
with independent coefficient, group and carrier universes. Given any predicate
`P` on smooth objects, `irreducibleSubquotientsProperty P A` requires `P D`
for every actual irreducible subquotient `D` of `A`. It imposes no length,
admissibility or finite-dimensionality condition.

The proof uses the Library's actual invariant submodule and module quotient
constructions. `actualCokernelIsColimit` proves that the actual quotient by the
image of an intertwiner is its categorical cokernel. Every intertwiner that
kills the image descends by the module quotient universal property; equivariance
is checked on quotient representatives. The quotient map is surjective and
therefore an epimorphism. Uniqueness follows by cancellation. Comparing this
cofork with the cokernel cofork of a short exact sequence identifies the actual
quotient with the third object.

Subquotient transitivity proves closure under subobjects and quotients, using
the actual injective and surjective maps corresponding to monomorphisms and
epimorphisms. Zero has no irreducible actual subquotients: an injective map into
zero forces its source to vanish, so any surjective image also vanishes,
contradicting the nontriviality of an irreducible representation.

For extensions, the published actual irreducible-subquotient dichotomy places
each irreducible constituent of the middle object in the image of the first
map or the quotient by that image. The image is an actual quotient of the first
object, and the categorical cokernel comparison identifies the other case with
a subquotient of the third object. Thus the constituent property is a Serre
class for arbitrary smooth objects.

The split short exact sequence of a binary biproduct gives binary product
closure. Zero and binary product closure give finite product closure. Mathlib's
abelian full-subcategory construction then supplies the inherited abelian
structure. The inclusion preserves kernels and cokernels, hence finite limits
and finite colimits.

This is derived infrastructure for actual inertia blocks and their generator
presentations. It composes the existing smooth-category abelianness, actual
subquotient transitivity and actual constituent dichotomy. The finite-product
and exact-inclusion steps use the same categorical construction as the
published `SimpleSupportFiniteClosureProof`, now with actual smooth
constituents. It proves no Bernstein decomposition, generator property or
compression stability assertion.
