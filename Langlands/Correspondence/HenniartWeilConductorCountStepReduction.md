# Counting reduction for the integer Weil conductor step

`Langlands.Henniart.Numerical.weilSwanBelow K k b` is the union, over natural Swan
exponents `s < b`, of the published torsion-number-one unramified-twist strata
`weilRefinedStratum K k s 1`. It uses the Library's rank convention `k + 1` and
allows `b = 0`. This is an internal cumulative stratum derived from the summands
of `weilConductorCount`, not a new literature target. It packages the two sets
of orbits compared in Henniart (1988), §3.4 (printed p. 509), for the counting
step in Corollaire 1.4.

## Implemented reduction

- The Artin conductor is unique: use the isomorphism of two representatives of
  the same class and `finiteInertiaConductorEquivalence` to compare their finite
  presentation sums. Unramified twisting preserves the inertia representation
  because the twist character is `1` there. Present the twist on the original
  finite Galois field and compare the descended Artin sums using that inertia
  equality. The two facts imply Swan uniqueness at a fixed rank on each
  unramified-twist orbit, regardless of which torsion numbers witness membership.
- Thus the cumulative stratum is a disjoint union over `Finset.range b`.
  `encard_weilSwanBelow` counts it by the sum of the extended cardinalities of
  these strata; it makes no finiteness claim about the individual strata.
- For `n = p^r`, `d ∣ n` and `l ≥ 1`, the Swan ranges in `weilConductorCount`
  at indices `n*l` and `n*l - 1` have lengths `d*l + 1` and `d*l`, respectively.
  In the second computation, `d*(n*l - 1) = (d*l)*n - d` lies between
  `(d*l - 1)*n` inclusive and `(d*l)*n` exclusive, using `0 < d ≤ n`.
- `weilConductorCountStep_of_equiv` takes a common type `Q` of extended cardinality
  `q_K` and, for every `d ∣ n`, an equivalence from `Q` times the shorter
  cumulative stratum to the longer one. Extended cardinality of a product yields
  the factor `q_K` at each `d`; distributivity yields it for the sum.

The reduction does not construct the equivalences or assert anything about
existence of character twists. Those ramification inputs are necessary for a
proof of the unconditional `WeilConductorCountStepStatement` and are not proved
here. The field and Weil representation carrier universes remain independent.
