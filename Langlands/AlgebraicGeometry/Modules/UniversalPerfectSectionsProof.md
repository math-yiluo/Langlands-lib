# Universal perfect representatives for smooth proper line-bundle sections: proof

Author: Worker 958.

The theorem `universalPerfectSections.{u}` proves
`UniversalPerfectSectionsStatement.{u}` with no extra hypotheses. Base rings,
scalar extensions and carriers stay arbitrary in universe `u`. The proof is a
single application of published results.

- `universalPerfectSectionsNoetherianReduction` proves
  `UniversalPerfectSectionsNoetherianReductionStatement.{u}`. That statement
  reduces the target over an arbitrary commutative base ring to the same
  assertion over noetherian base rings. It assumes properness descent and
  line-bundle descent to finitely generated subalgebras.
- `NoetherianApproximation.isProperSubalgebraDescent` proves the properness
  descent hypothesis, `IsProperSubalgebraDescentStatement.{u}`.
- `NoetherianApproximation.lineBundleSubalgebraDescent` proves the
  line-bundle descent hypothesis, `LineBundleSubalgebraDescentStatement.{u}`.
- `noetherianUniversalPerfectSections` proves the noetherian-base case,
  `NoetherianUniversalPerfectSectionsStatement.{u}`. Its scalar rings are
  still arbitrary.

Applying the reduction to these three proofs gives the target proposition
exactly.

## Mathematical content of the ingredients

Each step below is proved in the cited publication. This file adds nothing
beyond the application above.

The noetherian case takes a finite ordered affine cover. The published perfect
Čech representative gives one bounded finite projective complex `K`, which
computes the alternating Čech complex over the original base and over every
scalar algebra. The Čech resolution comparison
`CechResolution.nonempty_cechCochainComplex_iso` identifies each such Čech
complex with actual derived module sections. This covers both the original
base and each pulled-back base, for the quasi-coherent line bundle and the
separated structure map.

The reduction works with the finitely generated subalgebras of the base ring
over its prime subring, which are noetherian. It descends, in successive
stages, the scheme, smoothness, separatedness, properness and the line bundle.
This yields a smooth proper family `X₀ → Spec T` with `T` noetherian. That
family pulls back to `X` along `Spec R → Spec T`, and the line bundle descends
with it. The reduction takes the representative over `T`
and extends its scalars to `R`, using the published scalar-tower result. It
then transports the representative along the resulting isomorphisms of schemes
and of coefficients.

The source route in the Stacks Project (`perfect.tex`, Lemma 36.30.4, tag
0B91, and Remark 36.30.2, tag 0A1I) uses perfect proper direct image and
affine derived comparison. The Lean proof instead uses explicit Čech
complexes over a noetherian base and noetherian approximation, as described
above.

The proposition is objectwise. This proof asserts no naturality of the chosen
isomorphisms and no further compatibility. It also supplies no Künneth or
restriction-map comparison.
