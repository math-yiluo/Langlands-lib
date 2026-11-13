# Deligne's constant-locus and total residue-fibre conditions

This module constructs conditions (a) and (b) in Drinfeld 1976, Section 2 A,
printed p.110 (PDF p.4), opening paragraph, and combines them with the
stalkwise framed determinant predicate already constructed in
`DeligneDeterminantLattice`. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The preliminary sheaf data and frame are defined in the final paragraph
of printed p.109 (PDF p.3), continuing onto p.110.

The parameters are a commutative ring O, a positive integer d, an
O-algebra field F, a scheme S, and a ring map from O into the actual
global sections of S. All use the same universe. The input is the actual
`SheafPreDatum` consisting of eta, T, u and the rational frame, including
its grading, Pi compatibility and local generation. No representing or
universal object is an input.

## Structural and additive stalk constructions

`structuralStalkAddMap` applies the actual additive stalk functor to a
morphism of structural modules. `structuralStalkLinearMap` equips that
same map with linearity over the actual local ring O_(S,s). Its proof
represents a scalar by a germ, refines a representative of the module
element to a common neighborhood, and applies the compatibility of
germs with scalar multiplication and sectionwise linearity. This is
derived infrastructure, not an additional assumption on a stalk map.

`additiveStalkIso` uses preservation of neighborhood colimits by the
forgetful functor from O-modules to additive groups. Its inverse sends
the underlying additive element of an O-module germ to the same additive
stalk germ; `additiveStalkIso_inv_germ` proves this directly from the
colimit comparison identity. This comparison is about forgetting
scalars, and asserts no tensor/stalk comparison.

## Condition (a)

`piZeroSpace` is the subspace S_i of S where the actual degree-i
structural Pi map vanishes after residue-field pullback, using the locus
already defined in `DeligneLineSheaf`. `piZeroInclusion` is its actual
continuous inclusion. `componentOnPiZeroLocus` is the inverse image of
the genuine eta^i O-module sheaf along that inclusion.

`ConstantOnPiZeroLoci` asks, for every i in Z/dZ, that this inverse-image
sheaf be isomorphic to the constant O-module sheaf with fibre O^d. Here
constant means the sheafification of the constant presheaf. An
isomorphism is required to exist; a trivialization is not added to the
data. This implements the restriction and constancy in source condition
(a). No closed-subscheme structure or covering theorem for the S_i is
claimed.

## Condition (b)

`etaStalk` is the actual total eta stalk after restriction to O, and
`etaStalkPi` is the stalk of its constructed Pi multiplication.
`etaPiQuotient` is its quotient by the image of that operator. The source
is the total eta_s/Pi eta_s, as in the source, without selecting one
homogeneous component.

`tangentStalk` is the actual additive stalk of the total structural
module T, with its existing local-ring module structure.
`tangentStalkPi` is the local-ring-linear stalk of the structural Pi map,
and `tangentPiQuotient` is T_s/Pi T_s. `tangentPiQuotientFibre` extends
this quotient along the actual residue homomorphism O_(S,s) -> kappa(s).
Mathlib writes this scalar extension as kappa(s) tensor_(O_(S,s))
(T_s/Pi T_s), with the residue field on the left.

`uStalkAdd` is obtained from the actual sheaf map u using the additive
stalk comparison. `uStalkAdd_germ` proves that it sends a germ to the
germ of the given u section. `uStalkAdd_pi` represents an element by a
germ and uses the given sectionwise Pi compatibility to prove
u_s(Pi e) = Pi u_s(e).

`tangentPiFibreMap` composes the quotient projection with the
extension/restriction adjunction unit, namely t -> 1 tensor [t]. Its
vanishing on the Pi image is proved. `uResidueFibreMap` composes it with
u_s. `etaPiRange_le_residueKernel` proves that this composite annihilates
the eta Pi image; it does not assert equality with the kernel.
`piQuotientResidueMap` is its actual induced additive homomorphism from
eta_s/Pi eta_s, constructed by the quotient universal property. The
representative formula is proved in `piQuotientResidueMap_mk`.
`ResidueFibreInjective` requires this map to be injective at every point.
No arbitrary map between these quotients is supplied as input. The
additive formulation suffices to express injectivity; a separate
O-linearity structure on the induced map is not constructed here.

## Combined predicate and scope

`SheafPreDatum.Admissible` is the conjunction of
`ConstantOnPiZeroLoci`, `ResidueFibreInjective`, and
`DeterminantNormalized`, with the nonzero image of pi in F required by
the last construction. It packages the two conditions above and the
existing all-integer, stalkwise framed determinant normalization. The
latter still has its documented boundary: no comparison with an
independently constructed equality of exterior-power subsheaves is
proved. Accordingly this conjunction is a predicate on these constructed
sheaf data, not a theorem identifying it with a separately defined
Deligne moduli functor.

The stalk infrastructure and quotient construction are derived directly
from the stated sheaf operations and source map u. This unit does not
construct admissible isomorphism classes, base change, a PGL action,
representability, or a generic fibre, and proves no existence theorem
for admissible data. Specialization to actual Nilp algebras is available
through `NilpSheafPreDatum`.
