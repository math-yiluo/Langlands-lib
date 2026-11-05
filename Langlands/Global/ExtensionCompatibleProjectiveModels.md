# Projective models at full exceptional preimages

This derived construction supplies the common exceptional-set model choice in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10, especially p.10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For the original finite field extension K → L and a quasi-compact scheme X
with a specified immersion into projective n-space over L, the constructors
choose a finite exceptional set V of lower places and construct an actual
model over the L-integers outside the full upper preimage of V. They accept
arbitrary initial finite sets S of lower places and T of upper places.
The chosen V contains S and its full preimage contains T. Empty initial sets
and n = 0 are allowed.

The geometric data are `ProjectiveImmersionRingModelData` over that exact
upper integer ring, with its literal inclusion into L as the algebra map.
Thus they contain an actual scheme, an immersion into projective space of
the same dimension, a locally finitely presented quasi-compact structure
morphism, a Cartesian comparison with the original X along the original
field inclusion, and equality with the specified original projective map.
The field comparison is constructed, rather than assumed.

`numberFieldExtensionProjectiveModel` takes the original map between
number fields and all their finite places. Archimedean places do not enter
this integer-ring construction.
`curvePlaceExtensionProjectiveModel` takes a finite extension K → L with
a compatible constant-field tower k → K → L, perfect k, and the original
k → RatFunc k → L function-field presentation. No additional function-field
presentation for K is required by this constructor. The restriction map uses
all actual discrete curve places trivial on k. Neither finite constants nor
separability is required. All fields and schemes use an arbitrary common
universe. Perfectness is used for finite-pole exhaustion in the constructor;
the underlying place restriction does not need it.

The implemented proof first constructs the published finite coefficient
model of the specified projective immersion. The private finite-generator
argument places its coefficient subalgebra in an upper integer stage U
containing T: take the finite union of stages containing the ring generators
and use monotonicity and ring closure. This is the same elementary
finite-support argument used for individual arithmetic models.
Set V = S union the restriction-image of U. The full-preimage membership
laws show that U is contained in the full upper preimage of V. Monotonicity
therefore puts the coefficient subalgebra in the integer ring at that exact
preimage. Its literal inclusion gives the compatible algebra tower needed
by `projectiveImmersionCoefficientBaseChange`, which constructs the model
and retains both original-map comparisons.

This module supplies the arithmetic model choice at a full exceptional
preimage. It does not identify the upper integer ring with the lower ring's
integral closure or prove that the extension is finite locally free.
The integral Weil model, its generic fiber and the comparison of adelic
topologies remain separate obligations.
