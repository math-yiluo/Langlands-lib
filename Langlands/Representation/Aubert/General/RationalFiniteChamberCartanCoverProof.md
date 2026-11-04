# Actual full-center uniformizer charts from the supplied Cartan witness

`RationalPointFamily.rationalFiniteChamberCartanCover` proves the complete
`RationalFiniteChamberCartanCoverStatement`, with no additional outer hypotheses.
It retains genericity of `ν`, the supplied global `StandardCocharacterStatement`,
and all the actual geometric inputs of the statement.

The full-index Levi equals the actual rational-point group by
`levi_univ_eq_top`, using the standard-cocharacter premise and genericity.
Standard cocharacters for the finite root subsets give the standard-vector
premise of `finiteChamberCartanCover`. The published
`commute_uniformizerPowers` theorem, applied to the full index, puts the
common pairing kernel in the full abstract center of the actual group.

The supplied same-compact Levi compatibility includes the uniformizer
valuation formula in its `DominantCentralizerLatticeConclusions` conjunct.
`exists_rep_rationalCartanSet` therefore gives a uniform lower bound on
simple-root pairings, using the supplied finite lattice transversal.
`exists_cartan_levi` at the full index supplies the actual cover, with both
compact factors in the specified special compact subgroup. Its compactness
comes from the supplied `SpecialCompactProperties`.

These verified inputs specialize `finiteChamberCartanCover`, yielding positive
diagonal generators, one finite set of translates, natural coordinates, and
a final factor in the full group center. The same theorem supplies compactness
of the actual full central quotient when the simple-root type is empty.
The group topology is the canonical rational-point topology; smoothness of
the reductive group supplies finite type for its topological group laws.

This is an internal composition of published geometric and algebraic
lemmas. It does not construct the supplied joint geometric witness or prove
Haar-volume, coefficient-decay or square-integrability conclusions.
