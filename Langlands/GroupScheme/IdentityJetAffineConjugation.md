# Actual conjugation at the affine identity-jet point

Let `H` be relatively affine over `S`, and let `h` map `H` into the base change
of an affine ambient group `G` over `Spec R`. Let `g` be an actual section of
the base-changed ambient group. The scheme map `conjugatorProjection` expresses
this section in the fixed affine coordinates of `G`.

`parameterAffinePoint` is this actual section on an affine base open `U`.
`jetConjugatorPoint` pulls it back to the canonical affine chart of the actual
identity jet of `H` above `U`. Both use the coefficient `R`-algebra induced by
their actual maps to `Spec R`.

The theorem `jetConjugatorPoint_eq_parameterPullback` identifies the latter
point with restriction of `parameterAffinePoint` along the actual jet
projection's section-ring map. Its explicit algebra morphism parameter must
have underlying ring map exactly `projection.app U`; the affine chart
naturality law then proves the point equality.

`affineJetPoint_inner` proves the actual scheme-point identity: the canonical
jet chart mapped through `h` followed by the actual inner automorphism equals
the original canonical jet point conjugated by `jetConjugatorPoint`. The proof
views the chart as an actual test scheme over `S`, applies the actual
inner-isomorphism point formula, projects back to the original ambient group,
and preserves multiplication through the actual affine-coordinate group
isomorphism. An identity map compares the actual coefficient structure with
the canonical relative spectrum structure.

This is an internal consequence of the existing actual inner automorphism,
base-change point, affine chart, and actual jet APIs. It adds no smoothness or
flatness premise. It supplies the actual geometric conjugation identity;
comparison with `universalCutConj`, the orbit kernel, and quotient descent
remains to be combined with the original jet coordinate algebra comparison.
