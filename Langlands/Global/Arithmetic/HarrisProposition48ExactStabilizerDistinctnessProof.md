# Distinct Mackey components at the auxiliary place from B6

`Langlands.Global.Harris.proposition48ExactStabilizerDistinctness` proves
`Proposition48ExactStabilizerDistinctnessStatement.{uF, uV}` with the original
hypotheses at independent universe levels `uF` and `uV`.

The proof applies `proposition48ExactStabilizerDistinctnessReduction` to
`Langlands.Automorphic.cuspidalArithmeticSpectralTransport.{0, 0, uV}`. The latter
carries attached cuspidal spectra along number-field isomorphisms with cofinite
agreement of the Euler polynomials at corresponding places. The field universes
are zero here because the level fields and the two endpoint fields are in `Type`.
This supplies the transport used to start and end the isobaric chains at fields
identified with the endpoints of the prime cyclic tower.

The reduction uses the unique place of the normal closure above the auxiliary
place to obtain a solvable Galois group and a prime cyclic tower. Arthur–Clozel
III.4.2(c) supplies weak base changes along the tower. The chains end at Hecke
families of conjugates of the norm pullbacks of the Mackey characters. Harris's
exact-stabilizer condition (4.12) separates the local components of these
families for distinct double cosets. B6 then separates the components of the
original Mackey constituents at the places above the auxiliary place.

B6 and III.4.2(c) are premises, not conclusions. The reduction does not use
cuspidal spectral rigidity, the prime cyclic hypothesis on `D/E`, or the count
of Mackey classes; these remain in the unchanged target.
