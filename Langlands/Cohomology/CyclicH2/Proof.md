# Calculating the cyclic comparison on a two-cocycle

This module proves the published statement
`Langlands.Cohomology.CyclicH2.CocycleSumComparison.{u}` as the theorem
`Langlands.Cohomology.CyclicH2.cocycleSumComparison`, with exactly that type.
The statement and its conventions are recorded in the published Statement pair.

## What is proved

For every commutative coefficient ring `k`, every finite commutative group `G`
in the same universe with a supplied generator `g`, every representation `A`,
and every arbitrary unnormalized two-cocycle `c`, let `x` be an element of
`ker(ρ(g) − id)` equal to `∑_{i=0}^{n-1} c(g^i, g)`, where `n = Fintype.card G`.
Then the class of `c` under `groupCohomology.H2π` equals the image of `x` under
Mathlib's actual map `Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2`.
The group of order one is included, the sum includes the term `c (1, g)`, and no
invertibility-of-order hypothesis appears.

## The conditional calculation

The helper `cocycleSumComparison_of_chainMap` proves the same conclusion for
any chain map `φ` from the cyclic projective resolution to the bar complex that
satisfies two hypotheses. In degree zero, `φ` must commute with the two
augmentations to `k`. In degree two, `φ` must send the standard generator to
`∑_{i<n} [g^i | g]`.

The proof first uses `ExtComparison.groupCohomologyIso_hom_eq` (in the shared
namespace `Langlands.Cohomology.CyclicH2`) to identify the actual Ext-based
comparison with the cochain map induced by `φ`. Evaluation on
the degree-two generator gives the sum of `c (g^i, g)` for `0 ≤ i < card G`,
including `c (1, g)`. The calculation uses the free representation's universal
map and Mathlib's two-cocycle-to-cochain isomorphism.

The cochain map is then combined with the identity-on-components short-complex
isomorphism for the even degree of the alternating cyclic complex. Its homology
map equals the hom component of `groupCohomologyIsoEven`. The generic helper
`shortComplex_homologyMap_class` uses naturality of the quotient map and
injectivity of the cycle inclusion to compare representatives. Finally,
injectivity of `groupCohomologyIsoEven.hom` and the inverse-isomorphism identity
give the desired equality in group cohomology.

## The final theorem

`cocycleSumComparison` applies the helper to the explicit chain map
`cyclicToBar k g hg` from the companion module `BarComparison`. Its two
hypotheses are supplied by `cyclicToBar_f_zero_comp_π` and
`cyclicToBar_f_two_single` from that module.

## Provenance

The proof is an internal chain-level derivation from Mathlib, not a claim that
the explicit formula is quoted verbatim from a source. The published Statement
pair records the original cyclic-resolution conventions and their provenance.
Worker 53 implemented the conditional calculation and the Ext comparison.
Worker 262 implemented the chain map in `BarComparison` and assembled the final
theorem. Worker 28 supplied the exact interface and the positive bar-comparison
design; Worker 25 documented the published target.
