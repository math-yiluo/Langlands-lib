# Actual formal maps under equality of scalar structures

This module transports actual global formal-module data through an
equality of two `O`-algebra structures on the same coefficient ring `R`. It is
the global counterpart of the existing atlas scalar transports. It is needed
when an induced scalar structure and a supplied target structure give distinct
typed chart presentations. It asserts no new literature result.

The existing `ModuleLaw.reAlgebra` from `AtlasAlgebraTransport` transports the
formal module itself and is reused here. `Hom.reAlgebra` is
an `O`-linear equivalence between its actual integral formal Hom modules;
`Iso.reAlgebra` retains both actual formal inverse maps. Ambient
`RationalHom.reAlgebra` is an `F`-linear equivalence of the actual rational
tensor Hom modules, preserving rationalization of integral maps and rational
formal composition.

`OrderAction.reAlgebra` retains the complete acting order on the transported
module. The integral full-order Hom and Iso transports retain their actual
formal maps and inverse equations. The full-order rational Hom transport is an
`F`-linear equivalence of the actual rational centralizers. Its value in the
ambient tensor is exactly the ambient transport, and it preserves the specified
integral rationalizations, identity and composition.

`OrderAction.QuasiIsogeny.reAlgebra` retains the given forward and inverse
rational maps and their actual inverse equations. Its two projections are
exactly the full-order rational Hom transports. It preserves rationalization of
an actual isomorphism, inversion and composition of quasi-isogenies.

Every definition and equation eliminates the supplied equality of scalar
structures; at reflexivity it retains the original data. Thus no formal map is
chosen independently, no extra equivalence is assumed, and no point-evaluation
criterion is used. This module does not assert invariance under arbitrary changes
of the scalar action.

The parameters are arbitrary commutative rings `O` and `R`, two equal algebra
structures on `R`, a ring `D` over `O`, a field `F` over `O`, and finite coordinate
types. These rings may lie in separate universes. The quasi-isogeny transport
retains the existing assumptions that `O` is a domain and `F` its fraction
field. Supplied-target atlas chart formulas and framed-base comparison
compatibility remain further constructions.
