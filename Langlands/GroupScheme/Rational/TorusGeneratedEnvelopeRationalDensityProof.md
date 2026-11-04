# Rational density in the fixed ground-field torus envelope

Author: Worker 1436.

`Langlands.GroupScheme.torusGeneratedEnvelopeRationalDensity` proves the exact
published `TorusGeneratedEnvelopeRationalDensityStatement.{u}`. For every
infinite field `k : Type u`, every smooth connected affine group scheme `G`
over `Spec k`, and every actual `D : TorusGeneratedEnvelope G`, the actual
rational points are Zariski dense in `D.group.X.left`. The universe is
arbitrary. Imperfect fields and every characteristic are included, and no
density premise on `G` is used.

The proof supplies the published unconditional `torusFiniteGaloisSplitting`
to the published bridge
`torusGeneratedEnvelopeRationalDensity_of_finiteGaloisSplitting`.
That bridge obtains an actual finite Galois splitting field for each torus,
uses the norm-density theorem for tori, and passes density along the actual
dominant morphism furnished by `D.hasPointedTorusDomination`. Thus no
splitting witness or other structural proposition remains an argument.
The original fixed envelope and the original rational-point density
predicate are unchanged.

`TorusGeneratedEnvelope.rationalPointMeetingOpen` constructs an actual
rational point of the same representative meeting any supplied nonempty
Zariski open. The returned subtype includes a point of `Spec k` whose image
lies in that open. It applies the existing conditional selector with the same
unconditional splitting theorem. This construction requires only smoothness
and affineness of the ambient group; ambient connectedness is unnecessary.
The nonempty open is supplied, while the rational point is constructed.

The provenance is internal: this module specializes two published
interfaces, `Rational.TorusGeneratedEnvelopeDensity` and
`Torus.FiniteGaloisSplittingProof`. The source correspondence for the target
is recorded in its unchanged statement Markdown, through CGP Proposition
A.2.11 and its use in Lemma C.2.1. This module uses the implemented
finite-Galois norm-density route rather than adding a unirational
parametrization. It discharges the envelope density input of rational
lifting; it does not prove envelope normality, split-radical product
replacement, pseudo-parabolic descent, or the full rational-lifting target.
