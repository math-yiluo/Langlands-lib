# Maximality of the standard archimedean compact subgroup

`Langlands.Global.standardInfiniteCompactMaximality` proves the existing
`Langlands.Global.StandardInfiniteCompactMaximalityStatement`, with full type

```lean
∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
  StandardInfiniteCompactMaximalityStatement K n
```

Thus every subgroup `U` of the actual `InfiniteAdelicGL K n` whose carrier is
compact and which contains `standardInfiniteCompact K n` equals that standard
subgroup. All natural ranks, including zero, are covered. The compactness of the
standard subgroup itself is supplied separately by
`Langlands.Global.isCompact_standardInfiniteCompact`.

## Coordinate projections

The proof uses the published multiplicative homeomorphism
`archimedeanGLCoordinates K n` from the group built from the actual archimedean
completions to matrix units over the product of real and complex coordinate
rings. At each real place, the private `realProjection` composes this map with
the matrix-units homomorphism induced by first-factor projection followed by
evaluation at that place. The private `complexProjection` uses second-factor
projection and evaluation at a complex place.

The lemmas `continuous_realProjection` and `continuous_complexProjection`
derive continuity from continuity of the coordinate homeomorphism, coordinate
evaluation, and the induced matrix-units map. Consequently the image of a compact
subgroup under either projection is compact, as recorded in
`isCompact_realImage` and `isCompact_complexImage`.

For a unitary real matrix `q`, the compact-factor family with value `q` at every
real place and identity at every complex place assembles to an element of the
standard subgroup. Its projection at any specified real place is exactly
`Unitary.toUnits q`. The analogous family with identity on the real side and
constant `q` on the complex side gives the complex case. These are the lemmas
`realProjection_standard` and `complexProjection_standard`; they use
`ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL` to identify the
projection. If the standard subgroup lies in `U`, these witnesses show that
each projected subgroup contains every unitary matrix.

## Local maximality and subgroup equality

The private helper `maximality_of_local` assumes the local compact-overgroup
statement over the real and complex scalars. For any element `g` of a compact
overgroup `U`, the preceding image and containment lemmas allow that local
statement to be applied to each coordinate projection of `U`. The helpers
`real_unitary_of_local` and `complex_unitary_of_local` conclude that every real
and complex coordinate matrix of `g` is unitary. Over the real scalars this is
the standard orthogonal condition.

The published equivalence `mem_standardInfiniteCompact_iff` then puts `g` in
the standard subgroup. This proves `U ≤ standardInfiniteCompact K n`.
Antisymmetry with the assumed reverse inclusion gives equality.

The final theorem discharges both local premises using
`Langlands.Group.unitaryMatrixCompactOvergroup`, instantiated at `ℝ` and `ℂ`.
It therefore has no local maximality premise, positive-rank assumption, or
supplied invariant form. Neither the coordinate argument nor the imported local
theorem requires positive rank. Empty families of either kind of infinite place
cause no difficulty because the coordinate conclusions are universal statements
over the corresponding place types.

## Provenance

This is an internal structural proof of the published global target. It combines
the coordinate and compact-subgroup constructions in
`Langlands.Global.ArchimedeanGL` and `Langlands.Global.ArchimedeanCompact`
with the local theorem in `Langlands.Group.UnitaryMatrixMaximality`.
The existing target's historical motivation remains in its own Markdown; this
proof uses the coordinate argument above and makes no additional claim about
the proof route in the motivating literature.
