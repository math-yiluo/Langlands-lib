# Actual rational norm characters on the literal standard Levi subgroup

Authors: Worker 289 and Worker 34. Worker 34 identified the required actual
Levi topology and rational norm interface for the normalized unramified trace
calculation; Worker 289 implemented the construction and its proofs.

This internal adapter uses the exact `RationalPointFamily.levi i ν I`,
where `I` is a finite set of the existing simple relative roots and
`rootSet i ν I` is its literal character subset. It uses the published affine
standard Levi representative
`Standard.leviScheme i ν (rootSet i ν I)` and its published inclusion
`Standard.leviHom`. It does not supply new group or representation data.

## The actual point homeomorphism

The ambient rational-point group has exactly `RationalPointFamily.pointTopology`.
The literal Levi has the inherited subgroup topology. The scheme's own rational
points have exactly `PointTopology.rationalPointTopology`.
`leviRationalPointHomeomorph` specializes
`standardLeviRationalPointsHomeomorph` to the published closed representative
of this same all-test standard subgroup functor.
`Standard.isRepresentedBy_leviHom` supplies the representation equation and
`Standard.isClosedSubgroup_leviHom` supplies the closed immersion; affineness of
the representative follows from that closed immersion into affine `G`.
No connected-reductivity assertion about the representative is required.

The underlying multiplicative equivalence is proved equal to the existing
`standardLeviRationalPointsEquiv` for that inclusion. Its forward map is
literally `rationalPoints.map (Standard.leviHom i ν (rootSet i ν I))`;
the application theorem displays the ambient-point formula. Thus the
construction relates the canonical and inherited topologies on the original
objects, rather than specifying a transported topology as new input.

These topology results hold over any topological field and any affine `G`
with the displayed `i`, `ν` and `I`. They require neither genericity nor a
maximal split torus; the definitions retain their existing meaning in this
more general scope. All scheme and field universes are the arbitrary `u`.
The empty simple-root type and empty subsets are allowed.

## The full continuous rational norm family

Assume now that `F` is any nonarchimedean local field, with its existing
valuation and topology. For every actual rational character `χ` of the same
standard Levi scheme, `leviRationalNormContinuousCharacter` composes
`Plancherel.rationalNormContinuousCharacter` with the inverse point
homeomorphism. Its source is exactly the literal subgroup
`RationalPointFamily.levi i ν I`. Its continuity follows by composition,
without a norm-continuity premise.

The evaluation theorem on an arbitrary subgroup member `m` is

```text
fieldNormUnits F (rationalCharacterEval χ (leviRationalPointHomeomorph.symm m)).
```

On the image of a rational point of the actual Levi scheme, cancellation of
the homeomorphism and its inverse gives exactly
`fieldNormUnits F (rationalCharacterEval χ m)`. The construction therefore
retains the published actual normalized rational-character norms, including
their existing sign convention.

`leviRationalNormCharacters` exposes the underlying homomorphisms as one
family indexed by **all** actual rational characters of the same Levi scheme.
`continuous_leviRationalNormCharacters` proves continuity of each member.
Its evaluation theorem on scheme points agrees with the published
`Plancherel.rationalNormCharacters`. This family can be used directly as the
continuous norm-family input of the published unramified-character and
compact-stabilizer interfaces. No finite generation, finite-rank lattice,
unramified-torus parameterization or rational-character classification
assertion is added.

## Provenance and retained obligations

The dependencies are the published represented-subgroup topology,
standard Levi point comparison, standard closed representability,
`RationalPointFamily`, and `Plancherel.RationalCharacterTopology`.
The new proofs specialize those actual constructions, use extensionality
to compare their forward maps, and compose their continuous maps.
They add no claim translated from external literature.

The local-field scope allows both characteristics, arbitrary nonsplit and
non-quasisplit groups, and no separate topology on the Levi. This unit does
not use Langlands classification, character independence, the geometric
lemma, adjointness, cuspidal support or trace regularity. It does not prove
same-Levi induction independence, the dense comparison of induced traces,
or the whole rational exact finite-length K0 Weyl-conjugacy proposition.
