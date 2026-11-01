# Nontrivial-scalar standard rational descent

`nontrivialStandardRationalGluing.{u}` proves the unchanged published
`NontrivialStandardRationalGluingStatement.{u}`. It concerns compatible scalar
sections of the actual standard rational quotients over a presented strict
affinoid base, with compatibility in every ordered-pair actual intersection
quotient. The field is complete and ultrametric and has the explicit
nontriviality witness required by the statement. The conclusion is unique
lifting along the actual standard quotient base maps.

The implementation follows the scalar degree-zero reduction of Achinger,
*Introduction to non-Archimedean Geometry*, November 22, 2020, proof of
Theorem 7.0.1, pp.66–67. Its registered source is
`achinger-2020-non-archimedean-geometry-nov22`, SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`.
The proof uses the separately proved actual Laurent-split chase, universal
iterated Laurent scalar descent, all-unit standard descent, threshold
construction and standard-cover reduction comparisons.

The outer induction is on the tuple length. The empty tuple is retained:
the no-common-spectrum-zero hypothesis forces a zero base, and the
preparation lemma supplies the actual unique lift of the empty family.
For a fixed positive length, the inner strong induction counts the indices
whose entries are not units, using the finite cardinality of that subtype.

If all entries are units, the all-unit theorem applies. Otherwise the proof
chooses a nonunit index and swaps it with the last index. The formal standard
reindexing equivalence transports descent back after the induction step,
including the changed numerator presentation. A nonzero scalar with norm
uniformly strictly below some tuple value at every spectrum point is chosen
by `scalarUniformThreshold`.

Splitting by the last entry divided by this scalar gives the actual upper,
lower and overlap data of `StandardRationalLaurentReduction`. On the upper
base, the shortened tuple omits exactly the last entry and still has no
common spectrum zero. The outer induction applies to its shorter length.
The equal-locus comparisons identify its standard domains with the retained
original pullback domains. The omitted last pullback has empty locus and
subsingleton actual algebra, so the formal extension lemma restores the
full upper family.

On the lower base and the overlap base, the last entry becomes a unit.
All previously unit entries remain units under the actual bounded maps.
The private finite-count lemma proves strict decrease even if additional
entries also become units: every nonunit image injects, through the chosen
index permutation, into the original nonunit indices, and the chosen last
index is missing from that image. The inner induction therefore applies
to both entire mapped tuples. The literal standard pullback definitions
identify these results with descent of the lower and overlap pullback
families. Overlap descent implies the separation needed by the
Laurent-split chase, which supplies descent of the reindexed original
family. Reindexing then gives the required original family.

The threshold is the only part requiring nontrivial scalar valuation. The
actual comparison lemmas and unconditional binary Laurent gluing retain
zero and nonreduced bases, nilpotent entries, empty rational loci and scalar
maps into zero quotients. No function is inferred to vanish from its
pointwise spectrum values. The printed upper shortened list on Achinger
p.67 has inconsistent initial indexing; the implementation retains every
entry except the chosen last one, as its strict-threshold argument requires.
Berkovich's retained Trieste 2009 lectures, Exercise 2.2.2(ii), p.9, and
Fact 2.2.6(i), p.10, provide rational-domain and scalar-acyclicity context;
the source SHA256 is
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.

Worker 146 contributed the preparation and formal compatibility route;
Worker 101 the threshold and empty-case pair and actual transport;
Worker 84 the iterated Laurent construction; Worker 105 its all-unit
refinement; Worker 125 the scalar standard-cover reduction; Worker 572
the degree-zero Laurent chase, iterated scalar descent, all-unit adapter
and final induction. Independent acceptance and publication of the exact
proof remain separate from development compilation.

The scope is scalar degree-zero standard-cover descent at unit radii over
nontrivially valued complete ultrametric fields. It does not establish
higher Cech exactness, admissibility, finite-module descent, arbitrary
radii, trivial-scalar standard descent, the whole-spectrum assembly or
the relative parent theorem.
