# Polynomial primitive coordinates from pointed torus domination

This internal assembly works over an arbitrary field of prime characteristic.
Let a reduced actual corepresented group admit a pointed dominant morphism
from a finite-rank split torus and a specified finite set of primitive
coordinate functions generating its coordinate algebra. It admits polynomial
primitive coordinates over the same field, hence an actual isomorphism to a
finite-dimensional standard vector group.

The initial primitive generating family remains an explicit hypothesis.
The result does not prove its existence from unipotence or p-torsion, or prove
the full all-characteristic splitness statement.

`primitiveCoordinatesIso` is the general reconstruction step over a field.
A primitive family `y : Fin N → B` gives the natural group homomorphism to
the standard vector group. If `aeval y` is bijective, its underlying scheme
map is the spectrum of a ring isomorphism. Reflection of isomorphisms along
the forgetful functor from schemes over the field and the group-object
construction provide the actual group-scheme isomorphism.

`exists_pointed_primitivePolynomialCoordinates` assumes reducedness,
`HasPointedSplitTorusDomination`, and a finite set
`T : Finset (primitiveFunctions e)` with
`Algebra.adjoin k (Subtype.val '' T) = ⊤`. It returns `N`, primitive
`y : Fin N → B`, and bijectivity of `aeval y`. It keeps the arbitrary
universe `u`, prime characteristic, and original ground field. Finite and
imperfect fields and `N = 0` are included; no smoothness or connectedness
hypothesis is required at this stage.

The proof uses `exists_pointed_primitiveFrobGenerators` to obtain a finite
replacement `G`, an injective pointed Laurent pullback, and a finite orbit
set. It reindexes `G` by `Fin G.card`. The pullbacks lie in the indicated
finite orbit space. Injectivity of the Laurent pullback and of finite
encoding on that space therefore gives injectivity of the indexed
encodings. Their finite set is exactly the image supplied by the
Frobenius-generator theorem. The primitive independence theorem then gives
injectivity of `aeval y`. Equality of the generated algebras and the initial
generation hypothesis give its surjectivity.

`exists_vectorGroupIso_of_pointed_primitiveGenerators` applies
`primitiveCoordinatesIso` to those coordinates. The conclusion is an
isomorphism of actual group schemes over the original field, and the
dominating morphism is used with its existing pointed, dominant scheme
meaning. It is not assumed to be a group homomorphism or to extend over a
torus boundary.

Provenance is internal assembly of the published and submitted coordinate
interfaces described above. Worker 1353 authored the paired
`PointedLaurentCoordinates` and `PointedPrimitiveFrobeniusGenerators`
dependencies; Worker 1589 authored this assembly and the Laurent algebraic
and primitive-independence dependencies. The primitive polynomial relation
step is essential: linear encoding alone does not preserve arbitrary
products or imply algebraic independence.
