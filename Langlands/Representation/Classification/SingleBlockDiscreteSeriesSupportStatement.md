# Unitary cuspidal support for square-integrable GL representations

Author: Worker 320.

`Langlands.GLSingleBlockDiscreteSeriesSupportStatement.{uF,uV}` is a
proposition definition for the GL specialization of the published
[`GLDiscreteSeriesPositiveRootSupportStatement`](DiscreteSeriesPositiveRootSupportStatement.md).
It is derived from that product-Levi assertion by the constructed single-block
Levi equivalence; it introduces no new source-level classification assertion.
This module states the specialization without proving it.

For every prime `p`, field `F : PadicField.{uF} p`, supplied realization `T`,
positive rank `n`, and shape `C : BlockShape n` with `C.length = 1`, the input
is an actual complex representation `ρ` of `GL_n(F)` on an arbitrary
`V : Type uV`. The only representation hypotheses are irreducibility and
`T.IsSquareIntegrable ρ`. The latter is the existing analytic predicate:
admissibility, a smooth unitary scalar central character, and square
integrability of all descended absolute matrix coefficients for every Borel
Haar measure on the actual quotient by the full scalar center. No quotient,
cuspidal presentation, norm or Hermitian form is assumed for `ρ`.

The conclusion supplies a refinement `R` of `C`, an irreducible cuspidal
representation `ω` of `(C.flatten R).Levi F.Carrier` with an invariant positive
definite Hermitian form, and a real vector `t`. It retains the exact
`RelativeRegularComparison.IsPositiveRootParameter C R t` predicate. Its
strictly positive adjacent scalar-root coefficients use reciprocal fine-block
sizes in determinant coordinates. Equivalently, the size-weighted vector
has zero total and strictly positive proper prefix sums in the sole coarse
block. There is no assertion that the coordinates themselves are ordered.
The unrefined case is allowed and has parameter zero.

The actual source is

```
(innerInduced T C R (fineTwist T C R ω t 0)).ρ.comp
  (C.singleBlockLeviEquiv hC F.Carrier).symm.toMonoidHom.
```

`fineTwist` twists `ω` by the residue-normalized determinant powers `-t`
and pulls it to the actual refined Levi subgroup. `innerInduced` is normalized
induction along the actual upper refined parabolic inside the single-block
Levi, with positive half modulus and right translation. Finally the action
is pulled back along the inverse of the constructed single-block Levi
isomorphism to give a representation of the original `GL_n(F)`. This is an
explicit transport of the refined induction construction; no identification
with a separately constructed standard-parabolic induction carrier is asserted.

The conclusion gives a complex-linear intertwiner from this source onto the
original `ρ`, together with its surjectivity. The target carrier is exactly
`V`. It is neither replaced by a selected isomorphic representation nor
supplied with a section. The inducing and induced carriers lie in
`Type (max uF uV)`; the original carrier remains in `Type uV`. Field and
carrier universes are independent.

A proof must transport the original all-Haar analytic hypothesis to the
single-block Levi quotient by its full center, transport irreducibility,
apply the proved product-Levi support theorem, and pull its actual map back
through the same single-block equivalence. The theorem gives a support
quotient with the strict root parameter. It asserts no segment progression,
strong head, uniqueness, or segment classification. Its provenance is this
internal specialization of the named Library objects and assertion; no new
reading of the statement's original literature is claimed.
