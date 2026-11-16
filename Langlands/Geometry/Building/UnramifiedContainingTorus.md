# Generic tori containing a prescribed unit-fixed split source

This internal construction extends a supplied `UnitFixedIntegralTorusData M iS`
inside a smooth integral model `M` over the integers of any nonarchimedean local
field `F`, in an arbitrary universe. It applies
`HenselianTorusLifting.containingMaximalData` over the original valuation ring.
Its Henselian instance is the Library theorem
`Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer`.
The resulting integral relative torus has a closed inclusion and a maximal
residue inclusion. Its generic fibre contains the original source `S`, through
the inverse of the supplied source identification followed by the generic
fibre of the lifted containment map.

`UnitFixedContainingTorusData` retains that relative torus, inclusion,
closedness, residue maximality, and the generic source homomorphism with its
exact factorization equation. `genericTorus` and `genericInclusion` read its
generic fibre through the supplied model identification. `genericIsTorus`
uses the field comparison for relative tori; `genericClosed` uses base change
of closed subgroups and postcomposition by that identification.

The coefficient extension to the maximal-unramified integers is split:
`RelativeTorus.IsTorus.isSplitTorus_of_henselian` applies to its relative-torus
base change, since these integers are Henselian with algebraically closed
residue field. The arithmetic inputs are `fixedFieldIntegersIsHenselian` and
`fixedFieldResidueIsAlgClosure`. `unramifiedTorus` and `unramifiedInclusion`
use the actual coefficient pullback, and `unramifiedClosed` preserves the
closed inclusion by base change.

For the exact generic compatibility, the relative torus is read as an integral
model of its own generic fibre, with identity generic identification. Its
inclusion becomes a model homomorphism. The Library theorem
`IntegralModel.baseChangeGenericIso_naturality` then identifies the two
coefficient towers. The commutative torus isomorphism in
`unramifiedGenericIso` is precisely the group-scheme generic identification of
that coefficient extension.

The construction is derived from the named Library inputs, rather than a new
claim about the original literature. It supplies torus data for a later
apartment argument; it asserts no apartment containment.
