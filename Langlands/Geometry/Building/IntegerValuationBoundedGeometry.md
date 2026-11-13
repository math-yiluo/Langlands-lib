# Bounded-subgroup geometry for integer-valued buildings

This internal interface isolates three geometric inputs to the maximal-bounded
part of Kaletha--Prasad, Theorem 4.2.15(1), printed pp. 173--174 / PDF pp. 204--205.
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
It is a derived organization of the source argument, not an assertion that the
inputs follow from the supplied apartment data.

For the actual `IntegerValuationBuildingData v G`, the proposition
`HasAlgebraicallyBoundedGeometry` has exactly three fields:

- every actual one-stabilizer is algebraically bounded;
- every algebraically bounded subgroup of the original rational-point group has
  a common fixed point in the original quotient building;
- for each actual vertex, every point fixed by its one-stabilizer is that vertex.

The field has an arbitrary universe and an integer-valued valuation compatible
with its valuative relation. No topology or local compactness is used in this
generic interface or its supporting lemmas. Boundedness uses every actual global
regular function. The first field retains boundedness as a separate obligation;
the structure does not assert that any of the three fields can be constructed.

The supporting character-kernel lemma proves that every algebraically bounded
subgroup lies in the original `characterValuationKernel v G`. For each actual
rational character, its published universal regular section has a uniform bound
on the subgroup. Evaluate on every natural power of a subgroup element. The
integer logarithm of the valuation gives a uniform upper bound on all natural
multiples of the integer character value. The Archimedean property of the integers
forces that value to be nonpositive. Apply the same argument to the inverse to
get nonnegativity. Its value is zero, so the multiplicative valuation is one.
The regular section is identified with the actual character evaluation by
`rationalPointAlgebraHom_rationalCharacterSection`.

The maximality reduction begins with the boundedness field. A bounded subgroup
containing a vertex one-stabilizer has a common fixed point by the second field.
Its point is also fixed by the vertex subgroup, hence equals the vertex by the
third field. The character-kernel lemma then puts every element of the overgroup
in the character kernel; since it fixes the vertex, it lies in the original
one-stabilizer. This proves the `Maximal` predicate, including boundedness.

`MaximalUnramified.BoundedGeometryStatement` quantifies these same three inputs
over the actual inertia fixed field of every nonarchimedean local field. It uses
exactly the valuative relation prescribed by the published target.
`MaximalUnramified.valuation_compatible` proves compatibility of the constructed
integer valuation with that relation, using `valuation_isEquiv`.
`vertexOneStabilizerMaximalBounded_of_boundedGeometry` applies the generic
reduction and has the exact published target as its conclusion. Its geometric
premise remains unproved. It is not a proof of
`VertexOneStabilizerMaximalBoundedStatement` without that premise.
