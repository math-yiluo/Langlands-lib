# Actual component-indexed derived centralizers of a pinned model

Worker 634.

For an `AffineSimplyConnectedPinnedModel`, this internal module constructs a
finite family of actual closed reductive subgroup schemes, indexed by the
Cartan components of its full constant root datum. Every geometric fibre of
each member is simply connected.

For a component `c`, the complementary simple coroots define a closed split
subtorus in the original coordinate torus, hence in the group. The published
construction `splitTorusCentralizerDerivedModel` supplies an actual relative
centralizer and its relative derived group; `componentGroup c` is that derived
group. Its closed inclusion in the original group is retained.

The whole coordinate maximal torus factors through each complementary
centralizer, because it is commutative and contains the complementary torus.
The factored map is closed and maximal on each residue-field fibre: its
composite into the original group is exactly the supplied maximal torus.

All assertions are internally derived from the coroot-subtorus and relative
derived-centralizer constructions. This prepares the factor construction in
Conrad, *Reductive group schemes* (2014), Proposition 6.4.4, pp.232–233. The
module does not yet prove that the candidate groups are almost simple,
pairwise commuting or a product presentation, nor does it perform descent.
