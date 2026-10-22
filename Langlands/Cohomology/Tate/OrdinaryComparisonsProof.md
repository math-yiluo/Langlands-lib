# Ordinary cohomology and homology comparisons

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The theorem `ordinaryComparisons` has exactly the type of the published
proposition definition `OrdinaryComparisons`, in arbitrary common universe
`u`. It combines four comparison results: positive-degree restriction and
corestriction with ordinary group cohomology, and corestriction and restriction
in Tate degrees at most minus two with covariant group homology and ordinary
homological transfer, respectively. The ordinary transfer maps were constructed
independently on standard resolutions. The theorem quantifies over any
commutative coefficient ring, finite group and subgroup, representation,
and natural degree `n` with `[NeZero n]`; its homological degree is `-(n+1)`.

Each comparison is proved by dimension shifting, using the actual coinduced
replacement sequences and their proved acyclicity. The positive comparisons
start from the inclusion and coset-norm formulas on invariant representatives.
The negative comparisons use the explicit degree-minus-one boundary formulas
and continue through augmentation shifts. The negative identities are imported from the published
`NegativeHomologyComparison` and `NegativeTransferComparison` modules.
The comparison isomorphisms are
Mathlib's actual Tate-to-ordinary isomorphisms. This wrapper simply combines
the four established identities; it changes none of the target's hypotheses.

The statement follows the conventions in Serre, *Local Fields* (1979),
VII section 7, printed pages 118–119, and VIII section 2, printed pages 129–130.
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The implemented proof route is internal and described in the paired helper
Markdown. Serre formulates these conventions for abelian group coefficients;
the formalization uses linear maps and finite sums over any commutative ring.
The specific replacement sequences have proved scalar splittings, so the
proof adds no splitting hypothesis on the representation or an arbitrary
coefficient sequence. The stated comparison ranges exclude degrees `-1` and
`0`; they make no claim about ordinary cup products.
