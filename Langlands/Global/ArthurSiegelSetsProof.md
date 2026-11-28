# The Siegel partition and truncation bundle

`Langlands.Global.ArthurTruncation.arthurSiegelSets` proves
[`ArthurSiegelSetsStatement`](ArthurSiegelSetsStatement.md). For the given connected reductive
group over a number field, maximal split torus and generic cocharacter, it chooses a single
maximal compact subgroup `K` with `P₀(𝔸) K = G(𝔸)`. The intersection `K ∩ P₀(𝔸)` commutes with
the positive torus of every actual algebraic Siegel setup for these data.

## Constructing the common compact subgroup

`exists_compatible_parabolicIwasawaCompact` uses `genericMinimalParabolic` and
`standardMinimalLeviStructure` to identify the parabolic and rational Levi subgroup indexed by
the empty set. `IntegralIwasawaFamily.existenceStatement` supplies an integral family at the
finite places. `exists_leviCompatible_parabolicIwasawaCompact` patches this family using
`FinitePlaceGroupPoints.parabolicIwasawaStatement` at finite places and
`InfinitePlaceGroupPoints.leviCompatibleIwasawaStatement` at infinite places. It gives the
maximal compact Iwasawa subgroup as a coordinate subgroup. The archimedean compact subgroups
are chosen for `P₀` and its Levi. The proof therefore applies
`isPositiveTorusCompatible_coordinateSubgroup` to every eligible Siegel setup with the same
coordinate subgroup.

## Specializing the covering, partitions and truncation results

`arthurSiegelSetsStatement_of_iwasawa` applies the four statements for compact Iwasawa subgroups
to that `K` for every reflection datum `D` and bijective restriction of real character parameters
`hρ`. The theorem `arthurSiegelSets` supplies the finite-place existence theorem and discharges
each of the four inputs as follows.

- `iwasawaSiegelCovering` gives compact factors with compact subgroup `K` and one parameter `T₁`
  such that `P₁(F) S^{P₁}(T₁, ω) = G(𝔸)` for every standard `P₁`. [Siegel covering](ArthurSiegelCoveringProof.md)
- `iwasawaSiegelPartitionStatement_of_reduction` takes `parabolicSpacesComparison` and
  `iwasawaSiegelReduction` as inputs. For covering data as in the respective predicates and
  sufficiently regular truncation parameter, it gives the ambient and relative partition sums
  equal to one, with finite support on each rational coset space. [Siegel partitions](ArthurSiegelPartitionProof.md)
- `iwasawaTruncationIdempotent` gives constant-term vanishing where a testing fundamental
  weight is positive and pointwise idempotence of truncation for measurable, locally bounded,
  left `G(F)`-invariant functions at sufficiently regular parameters. [Vanishing and idempotence](ArthurTruncationIdempotenceProof.md)
- `iwasawaTruncationRapidDecay` takes a smooth structure and a closed matrix representation of
  positive size. At sufficiently regular parameters it gives decay by each inverse power of the
  adelic source norm on the norm-one part of each Siegel set of `K`. The input is a finite
  plot-smooth left `G(F)`-invariant function on the full adelic group with one moderate growth
  exponent for all enveloping derivatives. [Restricted rapid decay](ArthurIwasawaTruncationRapidDecayProof.md)

## Sources

- J. Arthur, *An introduction to the trace formula* (2005), in
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, §4, p. 24 for the choice of `K`,
  §8, pp. 37–40 for Theorem 8.1, Lemma 8.2 and (8.1), and §13, pp. 68–73 for
  Proposition 13.1(a),(b) and the restricted use of Proposition 13.2(a).
- J. Arthur, *A trace formula for reductive groups I* (1978), registered as
  `arthur-1978-trace-formula-reductive-groups-I`, §6, pp. 941–942 for the covering for standard
  parabolics, the reduction-theoretic input and Lemma 6.4.
- J. Arthur, *A trace formula for reductive groups II* (1980), registered as
  `arthur-1980-trace-formula-reductive-groups-II`, §1, Lemmas 1.1 and 1.4 for the vanishing
  and decay arguments used by the truncation inputs.
