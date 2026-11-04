# Bounds for conjugate-intersection indices

`DoubleCosetIndexBoundsStatement` is an internal algebraic target for the
full-center quotient volume estimates. For a subgroup `K` of an arbitrary
group `G`, the existing `doubleCosetIndex K g` is the natural-number index
`[K : K ∩ gKg⁻¹]`, with zero denoting an infinite index.

The statement has three conclusions. If the indices at `g` and `h` are finite,
the index at `gh` is finite and at most their product. A finite index at `g`
therefore bounds the index at every natural power `gⁿ` by the corresponding
power of the original index, including `n = 0`. Finally, applying any group
homomorphism `f : G → H` to both `K` and `g` preserves finiteness and cannot
increase the index. The universes of `G` and `H` are independent.

This target is derived from elementary relative-index arithmetic and invariance
of relative indices under conjugation. It has no topological or Haar-measure
hypotheses and does not itself establish finiteness for compact open subgroups,
contraction estimates, actual reductive volume estimates or integrability.
