# Repeated graded pieces and composition factors

Module `Langlands.Representation.Filtration.GradedRepetitionStatement`.

`Langlands.GradedFactorRepetitionCriterion.{uK,uG,uY}` is an internal,
derived formulation for representations of an arbitrary monoid `G` over a
field `k`. The coefficient field, acting monoid, and representation carrier
have independent universes. Worker 257 proposed this interface and the
multiplicity argument for the distinct supercuspidal product proof; Worker 122
formalized the statement. It is not a quotation from a source.

The statement takes an actual composition series `t` of a representation `Y`
with `N` simple graded factors, and any actual finite filtration `u` of the
same representation with `m` graded pieces. If distinct indices `i` and `j`
give equivalent graded pieces and the piece at `i` is nonzero, then there are
distinct indices `a` and `b` of `t` whose factors are equivalent. Nonzero means
`Nontrivial` of the actual carrier, and equivalence means an actual
`Representation.Equiv`.

The filtration `u` may have zero pieces, repeated steps, or nonsimple pieces.
The statement does not require a splitting or semisimplicity. Nontriviality
of the specified piece is essential: two zero pieces do not force repetition
in a composition series. The premise itself rules out incompatible zero-length
edge cases.

This is a statement only. Its intended proof chooses a simple constituent of
the first nonzero piece, transports its positive multiplicity to the second,
and uses additivity and Jordan–Hölder independence to force an ambient
multiplicity of at least two. The module imports only actual filtration
definitions; it contains no GL, Jacquet, segment, or classification input.
