# The central torus of a Levi adapted to a radical intersection

This is an internal composition of the published actual rational Levi,
solvable radical, all-test intersection, and whole-torus centralizer interfaces.
It isolates the largest-central-subtorus clause of
`ParabolicRadicalTorusLeviStatement`; it does not prove that proposition.

Over any field `k : Type u`, suppose `l : L → P` is an actual rational Levi,
`j : P → G` is closed, and `t : T → G` is a closed embedding of a commutative
group scheme with an actual factor `f : T → P`. Let `r : R → P` be a supplied
ground-field solvable radical. Suppose a torus `S` has a closed map
`sT : S → T` whose composite with `f` represents the entire intersection of
the ranges of `f` and `r` on every test scheme. Suppose `l ≫ j` represents the
whole-torus centralizer of `sT ≫ t`, and an actual map `sL : S → L` satisfies
`sL ≫ l = sT ≫ f`.

The theorem
`IsRationalLeviSubgroup.isLargestCentralSubtorus_of_radicalIntersection`
proves `IsLargestCentralSubtorus sL` under the additional local equality
`torusCentralizer t = SubgroupFunctor.range t`.
No reductivity or maximal-torus hypothesis on the ambient group is required
for this local form; its self-centralizing equality is an explicit premise.

The implemented proof first reflects closedness through the given closed
inclusions. The supplied centralizer representation makes `sL` central in `L`.
The range of `t` centralizes the image of `S`, because both factor through the
commutative group scheme `T`; hence `t` has an actual factor through `L`.
Every closed central torus of `L` therefore centralizes `t` after mapping to `G`.
The local self-centralizing equality places its range inside `T`, and
monomorphic cancellation reflects this containment into `P`.
The published theorem
`IsRationalLeviSubgroup.range_centralTorus_le_solvableRadical`
also places it in `R`. The supplied full intersection equality then places it
in `S`, and cancellation through `l` gives the required containment in `L`.
All containments include every relative test scheme and every refinement.

The construction `IsRationalLeviSubgroup.radicalIntersectionCenter` removes
the need to supply `sL`. It takes the same hypotheses concerning `S`, the
intersection, and its represented centralizer, together with the local
self-centralizing equality. It returns an actual morphism `sL` bundled with
`sL ≫ l = sT ≫ f` and `IsLargestCentralSubtorus sL`. Its morphism is the
published canonical `torusCentralizerFactor` of `sT ≫ t`; cancellation
through `j` gives the factorization inside `P`.

The auxiliary theorem
`IsCentral.range_comp_le_torusCentralizer_of_factor`
establishes the centrality-to-centralizer containment used here over any base
scheme, by mapping each commutation equality along the ambient homomorphism.
Its containing group, central subgroup, and ambient homomorphism have no
smoothness, affineness, or injectivity requirements.

The wrapper
`IsRationalLeviSubgroup.isLargestCentralSubtorus_of_structural_input`
uses an explicit proof of the published proposition
`MaximalTorusCentralizerStatement.{u}` to supply the local equality for a
maximal torus in a connected reductive group. It does not prove that structural
proposition or assume it globally. Neither form constructs a solvable radical,
an intersection torus, a rational Levi, or a whole-torus centralizer
representative. Maximality of `S` in the radical and geometric radical data
remain separate obligations of the host theorem.

The provenance is internal: the proof uses the published factorization and
closedness lemmas in `Rational.LeviFactorization`, the centralizer comparison
in `Rational.TorusSplitPartTransfer`, range-containment reflection in
`Rational.LeviCentralizerExtension`, and the central-torus radical containment
in `Rational.CentralLeviTorusRadical`. No new external mathematical theorem is
asserted.
