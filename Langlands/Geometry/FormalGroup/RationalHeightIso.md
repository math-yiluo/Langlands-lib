# Local rational heights under actual formal isomorphisms

This internal construction transports the existing local kernel-rank height
relation along specified actual isomorphisms of its source and target formal
modules. The source and target coordinate sets may differ, and all are finite.
The coefficient ring and the rational scalar field share a universe, as in
`RationalHeight`. The scalar ring is an arbitrary commutative ring.

For actual formal isomorphisms a from M to M' and b from N to N',
`Hom.isoTransport a b` sends f to b f a⁻¹. `RationalHom.isoTransport`
extends this linear map to the actual tensor Hom. The tensor formula is
composition with the rationalizations of the same actual isomorphisms.
These constructions commute with coefficient restriction on test algebras.

`RationalSection.isoTransport` is the actual sheafification of this natural
map of rational Hom presheaves. It agrees with transport of integral,
presheaf and global tensor sections, and commutes with restriction to every
open subset.

`RationalSection.HeightPresentation.isoTransport` retains the denominator
exponent and both kernel-rank exponents. It transports the numerator's actual
finite kernel representation and fppf lifting property through the supplied
isomorphism square. The source scalar-power kernel is transported through
the source isomorphism, which commutes with the scalar action. Thus the
signed rank difference is unchanged. Applying this construction on each
witnessing neighbourhood proves `HasHeightFunction.isoTransport`; its
global tensor consequence is `ofGlobal_isoTransport`.

The provenance is internal. The proof uses the existing actual formal
composition and coefficient extension, tensor linear extension, functorial
sheafification, and `Hom.hasHeight_of_isoSquare` from `KernelTransport`.
No height is assigned freely. No height uniqueness, additivity, coefficient
base-change theorem or representability assertion is made here.
