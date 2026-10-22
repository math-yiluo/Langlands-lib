# Ordinary corestriction index and tower laws

The theorem `Langlands.Continuous.ordinaryTransferLaws` proves exactly the
published proposition `Langlands.Continuous.OrdinaryTransferLaws.{u}`. It
establishes restriction followed by corestriction as multiplication by the
subgroup index, and transitivity of corestriction along a subgroup tower,
in every natural degree including zero. The coefficient ring is an arbitrary
commutative ring, the ambient group is finite, and all carriers share an
arbitrary universe `u`. The wrapper retains every finite instance and the
explicit subgroup-coordinate map quantified by the target.

Worker 25 wrote the Lean proof and this explanation. The proof imports the
published statement, `PositiveCorestriction`, and `TowerTransitivity` without
modification. Their dependencies supply the independently constructed ordinary
standard-resolution transfer and the proved Tate comparisons and laws. This
module adds derived proof lemmas and the final theorem; it does not define a
replacement transfer.

In degree zero, `ordinaryCorestriction_H0Iso` proves the commuting square
between actual ordinary corestriction, Mathlib's `groupCohomology.H0Iso`, and
`Langlands.Tate.cosetNorm`. The proof precomposes with the epimorphism from
zero-cocycles to cohomology and postcomposes with the inclusion of invariants
into the representation. Naturality of the homology projection and cycles
inclusion reduces the claim to `ordinaryCorestrictionCochainMap_zero`, the
published evaluation of the actual ordinary cochain transfer on invariant
zero-cocycles. Thus this square concerns ordinary H⁰ itself, before passage
to a quotient by norm images.

The two accompanying H⁰ squares identify ordinary subgroup restriction with
`invariantRestriction` and the tower coordinate map with `reindexInvariants`.
Both follow from Mathlib's `map_H0Iso_hom_f` after cancelling the invariant
inclusion. The tower coefficient isomorphism acts as identity on the underlying
coefficient module while identifying the two restricted actions.

Cancelling the target H⁰ isomorphism now reduces the zero-degree index law to
`cosetNorm_invariantRestriction`. Each coset acts trivially on an ambient
invariant, so the norm is the subgroup index times that invariant. The analogous
cancellation reduces the zero-degree tower law to `cosetNorm_trans`. That
published lemma reindexes the cosets of `K` in `G` by a coset of `H` in `G`
and a coset of `K.subgroupOf H` in `H`; it includes the same invariant coordinate
map used here. These zero-degree arguments do not use the positive-degree
comparison isomorphism.

In a degree `q` with `[NeZero q]`, the index proof first expresses
`corestriction_restriction` as an equality of module-category morphisms on Tate
cohomology. The proved identities `restriction_groupCohomology` and
`corestriction_groupCohomology` express those two maps through Mathlib's
`TateCohomology.isoGroupCohomology q`. Cancelling the source and target
isomorphisms gives the ordinary identity. Composition commutes with
natural-number scalar multiplication, so the coefficient on the identity
morphism remains exactly `H.index`, over any characteristic.

The positive-degree tower proof similarly starts from `corestriction_trans`.
The homomorphism of `towerReindex` is the published `reindex` map. Its
`reindex_groupCohomology` comparison gives exactly the ordinary map for
`Subgroup.subgroupOfEquivOfLe h` and `towerCoefficientIso h A`. Rewriting all
three corestrictions by their positive comparisons and cancelling the
intermediate isomorphisms proves the specified ordinary tower equation.
Finally, the wrapper splits each natural degree into zero or successor and
combines the corresponding index and tower lemmas.

The source convention is Serre, *Local Fields*, English translation by Marvin
Jay Greenberg, Springer, 1979, Chapter VII section 7, printed page 119
(PDF page 125). Serre defines corestriction in degree zero by the left-coset
norm, extends it uniquely to cohomology, and states the index identity in
Proposition 6. The tower law is derived from composition of norms and uniqueness
of that extension; it is not a separately quoted proposition on that page.
The implemented Lean route instead combines the explicit ordinary H⁰
calculation with the published Tate laws and comparisons in positive degrees.
Serre's abelian-group convention is applied here to the underlying additive
modules, with all maps linear over the arbitrary coefficient ring.

Registered source: `serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The norm and index assertions on the cited page were checked directly.
