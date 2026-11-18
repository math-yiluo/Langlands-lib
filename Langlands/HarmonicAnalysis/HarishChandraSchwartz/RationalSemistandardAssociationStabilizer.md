# Weyl stabilizer of an actual discrete-series orbit

Waldspurger's Remark VII.2.4 defines `Stab(O,M)` as the classes in
`W(G|M)` that preserve `O`. See *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, printed p. 320 (PDF p. 86), source
`waldspurger-2003-plancherel`. The Weyl transporter quotient is from V.1,
printed p. 288 (PDF p. 54).

`WeylOrbitStabilizer` is a subtype of the published
`SemistandardWeylTransporterQuotient` with source and target the same
literal Levi. Its condition is `WeylTransports` from
`RationalSemistandardAssociation`, which uses all-test Levi conjugation
and transport of the actual smooth-dual constituent set. The
transporter quotient allows inclusion of Levis. The spectral condition
requires equality of Levis, as supplied by `WeylTransports.levi_eq`
under the stated centralizer containment.

Every element of the actual `W^M` has a normalizer lift in the Levi.
Conjugation by that lift acts trivially on the constituent classes by
`OrbitConjugates.self_of_mem`. The transport condition is therefore
invariant under left multiplication by the target Weyl subgroup. This
gives `quotientWeylTransports` and its formula on each Weyl representative.
The stabilizer is nonempty by the identity class and is finite under
`IsConnectedReductive.finite_relativeWeylGroup`.

`weylOrbitStabilizerSubgroup` consists of the full relative Weyl elements
that preserve the same Levi and orbit. It contains `W^M`. Its left
classes modulo `W^M` are exactly `WeylOrbitStabilizer`, by the equivalence
`weylOrbitStabilizerEquiv`. The coset cardinality identity then gives
`|H| = |Stab(O,M)| |W^M|` for the full subgroup `H`, and
`card_weylOrbitStabilizer_pos` proves positivity of the denominator
under the geometric hypotheses. This denominator counts Weyl classes.
The orbit measure uses the stabilizer of a representation under unitary
unramified twisting.
