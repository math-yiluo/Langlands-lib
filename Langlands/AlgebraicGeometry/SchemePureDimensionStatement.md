# Pure dimension of locally finite-type schemes and their fibres

These derived statement targets support the pure-dimensional fibre clause
of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
They isolate locality and base-change prerequisites and do not assert
the source theorem's filtered descent or constructibility conclusion.

`LocallyFiniteTypePureDimensionOpenCover` states that, for any scheme X
locally of finite type over an arbitrary field k, pure dimension d is
equivalent to pure dimension d on every member of any actual open cover
of X. The cover index has an independent universe. The cover can have
empty members and need not be finite.

`LocallyFiniteTypeSchemeFieldExtensionPureDimensionInvariance` states
that every extension K/k preserves and reflects pure dimension d of X.
The scalar extension is the actual categorical pullback of the original
structure morphism along Spec K → Spec k induced by the algebra map.
No finiteness or algebraicity condition is imposed on K/k.

`LocallyFiniteTypeFiberPureDimensionBaseChange` considers an arbitrary
cartesian square with P mapping to X by a and to Y by b, over f : X → Z
and g : Y → Z. If f is locally of finite type, then for every y in Y,
the actual residue-field fibres of b at y and f at g(y) have pure
dimension d simultaneously.

`LocallyFiniteTypePureDimensionFibersBaseChange` states the resulting
all-fibres comparison: arbitrary base change preserves the condition,
and a base change surjective on underlying points also reflects it.
Surjectivity is retained only in this reflection assertion.

`SchemePureDimensionComparisons` groups the four propositions. The
fields and schemes occupy a common scheme universe, independently of
the open-cover index. All schemes and morphisms can be nonaffine and
nonseparated. Local finite type does not impose quasi-compactness or
quasi-separatedness. Pure dimension means the previously defined
componentwise topological Krull dimension, and empty schemes and fibres
satisfy it vacuously. It is not the weaker assertion that the whole
space has dimension d.

The intended proof uses the proved constancy of dimension on nonempty
opens of components of locally finite-type field schemes to establish
open-cover locality. Affine charts and their actual pulled-back affine
charts then reduce scalar extension to the finite-type affine algebra
comparison. The actual cartesian fibre isomorphism reduces the
pointwise assertion to the extension along the actual residue-field
map. Surjectivity supplies reflection at every original point.
These are proposition definitions awaiting independent proof publication.
