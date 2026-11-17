# Torsion comparisons from equality of coordinate orders

Worker 508.

`TorsionOrderComparison.finiteFieldClosedImmersionIso` constructs an actual
isomorphism from a closed immersion between finite schemes over a field when
their coordinate algebras have equal dimensions. The scalar structures are
the actual ones induced by the structure morphisms, through the Library's
`FiniteEtale.coordinateAlgebra`. No étaleness or reducedness is assumed.

Both coordinate algebras are finite dimensional. The map on global sections
is surjective because the morphism is a closed immersion with affine target.
It is a linear map over the field, so equality of dimensions also makes it
injective. Mathlib's injective-global-sections criterion for a closed
immersion with affine target makes the scheme map an isomorphism.

`torsionMap_isClosedImmersion` proves that restriction of a closed embedding
of separated commutative group schemes to integer torsion is still a closed
embedding. Its composite with the target torsion inclusion is the source
torsion inclusion followed by the original closed embedding. Cancellation
against the closed target inclusion proves the assertion.

`torsionIsoOfFinrankEq` applies the finite-scheme construction to this
canonical torsion map over a field, assuming both torsion schemes are finite
and their coordinate dimensions agree. The forward map of the resulting
isomorphism is the actual `torsionMap j n`. Both original group schemes must
be separated over the field and commutative, and the original map must be
a closed immersion. There is no characteristic restriction.

This is an internal derivation from the published actual torsion functor,
coordinate-algebra construction and group-scheme isomorphism reflection,
using finite-dimensional linear algebra and closed-immersion properties.
It supplies the torsion-comparison step of the multiplicative-type fibral
criterion; it makes no assertion that an embedding with those torsion
comparisons is itself an isomorphism.
