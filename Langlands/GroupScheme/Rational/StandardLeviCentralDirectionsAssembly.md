# Standard-Levi central directions from intrinsic structural statements

Authors: Worker 1322, Worker 1320, Worker 1327, Worker 1321, and Worker 1311.

This source-free derived assembly proves the exact unchanged
`StandardLeviCentralDirectionsStatement` from four existing intrinsic structural
propositions: `StandardCocharacterStatement`,
`DynamicCentralizerReductiveStatement`, `DynamicLieStatement`, and
`CharacterRestrictionStatement`, all at the same arbitrary universe.
`StandardLeviCentralDirectionsReductionStatement` is precisely this implication;
`standardLeviCentralDirectionsReduction` proves it. None of those four structural
propositions is proved here, so this contribution does not complete the
unrestricted host proof task.

`standardRootAnnihilatorRank_of_standardCocharacter` first uses standard
cocharacters for every face. The published standard-cocharacter finiteness
module pairs a cocharacter for the complement of each singleton with an
integer linear relation to prove independence of the actual simple roots.
Finite generation of the actual split-torus character lattice then gives their
finiteness. Flat rational scalar extension preserves that independence, and
restriction to the selected subset preserves it again. The existing actual
split-torus real dimension and simultaneous-evaluation rank-nullity theorems
give all five conclusions of `StandardRootAnnihilatorRankStatement`. This route
does not assume a separate relative-root-system realization.

For every actual closed representative `j : L → G` of the choice-free standard
Levi, the standard-cocharacter proposition identifies that same all-test
subgroup functor with the dynamic centralizer of a supplied standard cocharacter.
The dynamic reductivity proposition therefore makes this actual `L` connected
reductive, without replacing the representative.

For every supplied split component `a : A → L`, the actual standard-Levi
containment theorem supplies a closed compatible morphism `f : A → T`,
injective on real cocharacters, whose real image contains the selected-root
annihilator. Standard-cocharacter existence and finiteness discharge that
theorem's structural premises. The forward-image theorem, using the dynamic
Lie proposition, gives the opposite containment for the same `f`, hence equality
of the actual image submodule with the existing `rootAnnihilator T J`.

The finrank of the range of the injective actual cocharacter map is the finrank
of its domain. Splitness of the supplied component identifies that domain
dimension with `splitTorusRank A`; substitution into the selected-root
codimension formula gives the required sum of ranks. Finally, the existing
rational character-restriction adapter applies integral injectivity and finite
index, supplied by `CharacterRestrictionStatement` for this connected reductive
`L` and this component `a`, to prove the rational-character rank identity.

Every map and subspace is the published actual construction. No basis, rank,
embedding, image equality, or desired geometric realization is assumed in the
reduction. The four retained premises are independently stated structural
propositions. Arbitrary fields, nonreduced relative roots, empty selections,
and rank zero are retained. The proof is an internal composition of existing
results and uses no external literature assertion.
