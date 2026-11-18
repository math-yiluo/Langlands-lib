# Actual integral-unit conjugation of special formal atlases

This internal construction lifts the actual integer-unit conjugation and inverse
formal maps from `DivisionOrder` to special formal modules and original special
atlases. It gives actual comparisons in the existing unframed equivalence
relation, including its height-certified variant.

The hypotheses are a nonarchimedean local field `K`, a finite-dimensional central
division algebra `D`, a supplied embedded field `ι`, and a commutative
`𝒪[K]`-algebra `R`. Special objects retain their existing
`IsUnramifiedSubfieldOfReducedDegree` certificate and their geometric tangent
character condition. No Hasse invariant, existence of the embedded field or
existence of a special object is proved here.

`BasicAtlas.OrderAction.twist` replaces every chart action by its precomposition
with an actual order-algebra automorphism and retains the original transition
maps. Transition equivariance is the original equivariance applied to the image
of the order element. `SpecialModule.twistIntegerUnit` and
`SpecialAtlas.twistIntegerUnit` specialize this construction to the actual
integer-order automorphism `a ↦ u⁻¹ a u`. Their underlying formal module or atlas
is exactly the original one. The special tangent certificate is transported
through `DivisionOrder.twistUnitIso` by
`HasGeometricTangentCharacters.ofIso`.

`twistIntegerUnitIso` has forward formal map given by the action of `u⁻¹` and
inverse formal map given by the action of `u`. For atlases these are the actual
compatible formal endomorphisms on every original coefficient test. Their
order-equivariance and inverse equations are the original coordinate-module
unit-isomorphism equations on each test, assembled by formal-map extensionality.
They do not rely on detecting rational tensors from pointwise values.

`twistIntegerUnitComparison` is exactly the original comparison induced by this
integral atlas isomorphism on the reflexive common refinement. Consequently
`classOf_twistIntegerUnit` proves equality in the existing comparison quotient.
The underlying scalar formal laws and their kernels are unchanged, so the
actual rank-based height predicates are equivalent by definition. The
height-certified atlas construction retains that same certificate and also has
the same comparison class.

Coefficient extension commutes with the twist for coordinate modules and for
atlases. For supplied coefficient algebras the proof first commutes the actual
extension and then transports across the proved equality of scalar-algebra
structures. The scalar transport lemma uses equality elimination.

The provenance is internal: the algebraic input is the previously constructed
actual order conjugation and its specified inverse formal maps; the specialness
input is transport of geometric tangent representations by those maps; the
quotient input is the existing induced-comparison construction. The source
motivation is Drinfeld 1976, §2 A, printed p.109, as recorded in `DivisionOrder`.
This file proves the unframed unit-isomorphism consequences. Transport of a
complete framed triple, the full division-group action and the matrix-group and
Frobenius parts of Drinfeld's action remain further constructions.
