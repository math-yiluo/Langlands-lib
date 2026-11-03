# Split root data and actual field extension

Worker 416. This internal prerequisite defines canonical transport of integral root
data and states its compatibility with the root datum of an actual split maximal
torus. The compatibility statement is not proved in this module.

## Canonical lattice transport

For commutative integral domains `k` and `K`, any morphism `b : Spec K ⟶ Spec k`,
and a split commutative torus `T` over `k`, `SplitRootDatum.baseChange b T hT P`
transports an integral root datum `P` using the published canonical additive
equivalences on actual character and cocharacter lattices. The root index type
is unchanged. The construction is Mathlib's `RootPairing.map`, applied to the
identity equivalence of indices and the integral linear equivalences associated
to these two additive equivalences.

The root and coroot formulas are definitional: both are the published actual
pullback maps. `baseChange_pairing` cancels the inverse lattice equivalences in
the transported perfect pairing. If the old pairing is the actual
`latticePairing T`, `baseChange_toLinearMap` proves that the new pairing is the
actual lattice pairing on the pullback torus. Its proof uses surjectivity of
the two equivalences and the published `latticePairing_baseChange`.

`baseChange_reflection` follows from the integral reflection formula, the
pairing identity, and additivity of the actual character map.
`map_corootSpan` applies the linear-map image-of-span identity to the range of
the coroots. The submodule order isomorphism induced by the cocharacter linear
equivalence then proves `corootSpan_eq_top_iff`. Thus the **integral** coroots
generate the whole cocharacter lattice before transport if and only if they do
after transport. No rationalization is used. These transport lemmas allow an
arbitrary root index universe independently of the ground-field universe.

## Actual root-datum compatibility target

`SplitRootDatumFieldExtensionStatement` quantifies over arbitrary fields `k`
and `K` in universe `u`, an arbitrary `k`-algebra structure on `K`, a connected
reductive group `G`, a split torus `T`, a maximal torus inclusion `i : T ⟶ G`,
and any supplied root datum `P` of `i`. It asserts that the transported datum
is `IsRootDatumOf` the **actual** pullback of `i` along the spectrum of
`algebraMap k K`. The root index type in this target is also in `u`.

The predicate `IsRootDatumOf` retains all its published clauses: the actual
lattice pairing, equality of the root range with the actual adjoint roots,
and normalizing rational-point representatives acting by the datum's
reflections. Affineness of the pullback is supplied by stability of affine
morphisms under pullback. No perfection, characteristic, separability,
algebraicity or finiteness condition is imposed on the field extension.

This is an internal compatibility target between existing Library
constructions, not an additional existence or classification theorem. Its
provenance is the actual Hom-lattice pullback in `Torus.SplitLatticeBaseChange`,
the published root-datum predicate in `Reductive.RootDatum`, and Mathlib's
transport of root pairings. This module proves the formal transport identities
above; it does not prove equality of actual root sets under field extension or
base change of normalizing representatives. Those geometric steps remain
obligations for a proof of the compatibility statement. In particular, this
unit does not prove simple connectedness is preserved by field extension.
