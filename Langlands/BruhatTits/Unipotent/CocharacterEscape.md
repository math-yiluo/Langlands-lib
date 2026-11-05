# Compact escape from a positive torus character

This internal geometric lemma uses the published intrinsic cocharacter
evaluation and the closed-embedding theorem for rational-point maps.
Worker 485 supplied the character-detection route in the norm-kernel geometry
audit; the present unit implements it.

The definition `cocharacterPointPowers i ζ t` is the ambient sequence
`n ↦ cocharPoint (groupHom ζ ≫ i) t ^ n`. It records the specified
cocharacter value without making any topological or positivity assumptions.
The subsequent theorems prove compact escape of this sequence under the
hypotheses below.

Let a commutative affine group scheme map by a closed immersion into an affine
group scheme over a Hausdorff topological field. Fix a cocharacter `ζ` and a
field unit `t` whose powers tend to zero. If one integral character `α` has
strictly positive pairing with `ζ`, the powers of the image of `ζ(t)`
eventually avoid every compact subset of the ambient rational points, for
their canonical point topologies.

For an ambient compact set, its inverse image in the source is compact because
the rational-point map is a closed embedding. Evaluating `α` and then taking
the field value gives a compact, hence closed, field subset excluding zero.
On the powers of `ζ(t)`, intrinsic evaluation computes this field value as
`((t : F) ^ n) ^ d`, where `d` is the positive integral pairing converted to
a natural number. These values tend to zero, hence eventually avoid the
closed image. This forces the original powers outside the ambient compact
set.

The module also proves equality of intrinsic torus evaluation with the
`cocharPoint` convention used by the contraction modules and states compact
escape in that convention. This identification needs no topology or closed
immersion hypothesis; the escape theorem uses the displayed affine,
topological-field and closed-immersion assumptions.

No nontriviality theorem for a unipotent radical, reductivity, norm-kernel
membership or Iwahori-basis existence is asserted here.
