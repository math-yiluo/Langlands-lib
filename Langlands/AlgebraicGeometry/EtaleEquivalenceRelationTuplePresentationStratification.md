# Triviality over the complement of the next tuple threshold

This module is derived infrastructure for the symmetric tuple stratification
in Stacks Project, Lemma 68.8.3 (Tag 0BBN), and its finite version in Lemma
68.8.6 (Tag 07ST). The registered originals are
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. The parameter `n` means
`n+1` entries. The result provides a scheme-theoretic identity relation over
the complement of the next threshold in a finite tuple tail.

The hypotheses are separated source, affine object and relation schemes,
and a closed joint endpoint map, in arbitrary scheme universe `u`.

`tupleFiniteZeroObjectMap_threshold_preimage` identifies the inverse image
of any total threshold under the original zero-component inclusion with
the original threshold. Its proof uses the component threshold formula
and the established threshold comparison under the one-entry tuple
isomorphism.

`tupleChart_factors_unit_of_not_threshold` applies to a finite family with
a chart strictly shorter than every other chart. For an arbitrary test
scheme and a map to the total relation, pointwise avoidance of the next
threshold by its source implies that this map is its source followed by
the unit. Threshold invariance also gives avoidance by the target. Joint
surjectivity of the coproduct inclusions and the strict length condition
force the map into the shortest chart's self-correspondence. Factoring
through this open component works on arbitrary schemes. The established
self-correspondence theorem then equates its two endpoints as morphisms.
The total relation's endpoint extensionality identifies it with its unit.
No factorization through a reduced degree scheme is assumed.

`tupleChart_unit_isPullback_of_not_threshold` expresses this universal
factorization as a source pullback square over any scheme whose image
avoids the next threshold. Its proof constructs the unique lift of each
pullback cone from the cone's map to that scheme.

`tupleTailNextComplementClosed` is the closed complement of threshold
`p+1` in the tail of charts with indices at least `p`, through `N`.
`tupleTailNextComplementScheme` equips it with the canonical closed
scheme structure from its vanishing ideal.
`tupleTailNextComplementι` is the closed immersion.
The module proves its closed immersion instance, the complement's
affineness, its image formula `tupleTailNextComplementι_range`, and
pointwise avoidance in `tupleTailNextComplementι_not_mem_threshold`.
These follow from the corresponding vanishing-ideal subscheme facts.

When `p < N+1`, the tail has a unique shortest chart at `p`.
`tupleTailNextComplement_unit_isPullback` specializes the arbitrary-scheme
pullback theorem to the canonical complement.
`tupleTailNextComplementCrossIso` identifies this complement with the
source pullback of the whole tail relation, by uniqueness of pullbacks.
Its two forward projection equations and
`tupleTailNextComplementCrossIso_inv_eq_snd` identify the isomorphism
explicitly.

These are comparisons within the existing tuple presentations. They do
not assert the existence of a Noetherian first level.
