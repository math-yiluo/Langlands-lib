# Homogeneous Pi iterates and rational component isomorphisms

This module constructs the actual homogeneous iterates of the operator on a
`LatticePiSheaf` and proves that each degree-one component map becomes an
isomorphism after rationalization. Its forward map is the rationalization of
the given integral component map. Its inverse is constructed from the other
`d - 1` component maps and multiplication by the inverse of the image of `π`.
The construction is natural in genuine homogeneous lattice morphisms.

## Source and provenance

The original input is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
At the end of printed p.109, Drinfeld defines the cyclically graded algebra
`O[Π] = O[X]/(X^d - π)`, with coefficients in degree zero and `Π` in degree
one. The first of Deligne's four data is a flat graded sheaf over this algebra;
the fourth is a rational frame in degree zero. The conditions continue on
printed p.110.

`LatticePiSheaf` supplies the actual coefficient-module sheaf,
flat stalks, homogeneous inclusions and component maps of multiplication by
`Π`. This module derives finite iterates and their inverses from those data.
These are implementation lemmas and constructions implied by the algebra
relation, not separately stated theorems attributed to Drinfeld. The module
imports `DeligneIsomorphism` by Lean name and uses its category of genuine
homogeneous lattice morphisms.

## Assumptions and actual objects

The common universe is `u`. The integral constructions use a commutative ring
`O`, an element `π : O`, a natural number `d`, a topological space `X`, and an
actual `M : LatticePiSheaf d π X`. The degree indices are `ZMod d`. The
complementary path and rational isomorphisms require `NeZero d`. For the
rational constructions, `F` is a field with an `O`-algebra structure and the
explicit hypothesis `algebraMap O F π ≠ 0`.

No local-field or nilpotence assumption is needed for this algebraic
construction. The specialization to Drinfeld's setting satisfies these more
general hypotheses. The existing flat-stalk field of `M` is retained as part
of the object but is not needed in these proofs.

`moduleSheafScalar a M` is the actual sheaf endomorphism whose underlying
natural transformation is `a` times the identity. Its naturality is proved on
sections using linearity. The scalar extension functor sends this map to the
endomorphism given by the image of `a` in `F`
(`rationalPresheaf_map_moduleSheafScalar`). The proof compares maps out of
extension of scalars on the generators `1 ⊗ m` and uses linearity of the
extension/restriction adjunction unit.

## Integral iterates and the cyclic relation

`LatticePiSheaf.piIterate i n` maps component `i` to component `i + n` by
composing the actual degree-one maps, with equality transports for cyclic
index arithmetic. At `n = 0` it is the equality transport from `i` to `i + 0`.
`homogeneousTransport_inclusion` states that an equality transport commutes
with the actual inclusions into the total sheaf.

`piIterate_inclusion` proves that the composite of this homogeneous iterate
and the target inclusion equals the source inclusion followed by the `n`th
power of the total operator. Induction uses the degree-one inclusion square
and the preceding transport identity. `latticePi_sheaf_pow_apply` identifies
powers of the total sheaf map with powers of its section maps;
`latticePi_sheaf_relation` then obtains its `d`th-power scalar relation from
the existing actual coefficient action.

`piCycle i` closes the `d`-step path by the equality `i + d = i` in `ZMod d`.
`piCycle_eq_scalar` says that it is multiplication by `π` on component `i`.
The proof composes with the actual monomorphism into the total sheaf, applies
the total relation, and uses scalar naturality.

`piReturn_degree` proves `(i + 1) + (d - 1) = i` using `d ≠ 0`.
`piReturn i` is the corresponding actual path of `d - 1` forward maps, from
component `i + 1` back to component `i`. `piReturn_inclusion` identifies its
composite with inclusion with the complementary total power. The lemmas
`pi_comp_return` and `return_comp_pi` prove both scalar composite identities:
forward Pi followed by the return path is multiplication by `π` on component
`i`, and the reverse composite is multiplication by `π` on component `i + 1`.
Both proofs cancel the actual monic homogeneous inclusion and reduce the
product of total powers to the same `d`th-power relation. This includes `d = 1`,
where the return path has zero steps.

## Rational component isomorphisms

`LatticePiSheaf.rationalPiPresheafIso F M hπ i` is an isomorphism between
scalar-extended component presheaves. Its forward map is scalar extension of
`M.pi i`; its inverse is `(algebraMap O F π)⁻¹` times scalar extension of
`M.piReturn i`. The two integral scalar composite identities pass through the
functor. Linearity of composition and the scalar extension lemma reduce each
inverse identity to `π⁻¹ · π = 1` in `F`.

`rationalPiIso` applies actual sheafification to this presheaf isomorphism.
Thus it is an isomorphism from `M.rationalComponent F i` to
`M.rationalComponent F (i + 1)`. `rationalPiIso_hom` identifies its forward
map with `(rationalSheafFunctor F X).map (M.pi i)`.

`rationalPiIterateIso` recursively composes these degree-one isomorphisms to
obtain an isomorphism from degree `i` to degree `i + n` for every natural `n`.
`rationalPiIterateIso_hom` proves by induction that its forward map is exactly
the rationalization of `piIterate i n`, including all index transports.

`rationalComponentFunctor F i` takes a genuine homogeneous lattice object to
its rational component in degree `i`. `rationalPiNatIso F hπ i` is the natural
isomorphism from this functor to the functor taking degree `i + 1`. Naturality
is obtained by applying rationalization to the already proved Pi-commutation
square for genuine lattice morphisms.

## Scope

All maps, inclusions and scalar extensions here are constructed from the actual
sheaves. The rational inverse is built before sheafification, so the proof
does not require preservation of monomorphisms or an unproved decomposition
of the total rational sheaf. This module supplies the component isomorphisms
needed to construct a rational frame in a shifted degree. It does not
construct that frame, the normalized projective action, preservation of all
four-data admissibility conditions, base-change comparisons, exterior
subsheaf comparisons or representability. The Library constructs the shifted
frame in `DeligneFramedShift`, the projective action in
`DeligneProjectiveAction`, shift base-change comparisons in
`DeligneShiftBaseChange` and the exterior subsheaf comparison in
`DeligneDeterminantSubsheaf`.
