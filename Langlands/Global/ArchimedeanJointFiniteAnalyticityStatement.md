# Real analyticity from the actual finite joint differential orbit

Authors: Worker 94 and Worker 116.

`Langlands.Global.ArchimedeanGL.JointFiniteAnalyticityStatement K n`
asks that every actual smooth complex-valued function with finite joint
central-and-compact differential orbit is real analytic at every actual
matrix unit. The number field has arbitrary universe `u`, and the rank
is any natural number, including zero.

The hypothesis `IsJointFinite K n f` is exactly
`Module.Finite ℂ (jointOrbitSpan K n f)`. This is the complex linear span
of the actual differential translates

```text
envelopingAction K n (centerInclusion K n z * b.val) f
```

for every `z : EnvelopingCenter K n` and
`b : compactEnvelopingSubalgebra K n`. The compact subalgebra is generated
by the complexified skew-adjoint matrix Lie directions. No finiteness of
the entire smooth-function space is assumed.

The conclusion is exactly
`∀ g : ArchimedeanGL K n, AnalyticAt ℝ (coordinateExtension K n f)
(g : ArchimedeanMatrix K n)`. Here `SmoothFunctions` is the published
submodule of complex-valued functions on the completion-based general
linear group, with real smoothness expressed through
`archimedeanGLCoordinates`. The published coordinate extension uses the
inverse open units chart and this coordinate equivalence. At each unit,
`coordinateExtension_apply` identifies it with the original function in
mixed coordinates. `ArchimedeanMatrix K n` is the original real matrix
space over the mixed product of real and complex infinite places; the
existing matrix norm and topology are used unchanged. Thus both real
directions at every complex infinite place are retained. The function
values remain complex, and the analyticity scalar is explicitly `ℝ`.

The conclusion quantifies over every unit, independently of its connected
component. It asserts local real analyticity at each of those points.
The coordinate extension away from the open units set has no asserted
regularity. The proposition assumes neither an elliptic differential
equation nor analyticity, a symbol certificate or an analytic-regularity
theorem. It places no nonzero-function, positive-dimension or
positive-rank restriction.

This is an internal concrete smooth-function specialization of the local
elliptic argument in Harish-Chandra's *Two theorems on semi-simple Lie
groups*, section 17, Lemma 33, printed pages 108–109 / one-based PDF pages
35–36. The original lemma concerns distributions whose orbit under the
product of the ambient enveloping center and the compact-direction
enveloping center is finite dimensional. The full compact enveloping
orbit in the present hypothesis is stronger. The proof constructs a
central signed difference of compact and complementary square sums.
Adding twice the compact square sum gives the full sum of squares;
finite-dimensionality supplies a monic polynomial annihilator. The proof
then invokes analytic elliptic regularity for that polynomial
differential operator.

The subgroup conventions need care. Section 16 of *Two theorems*, printed
page 106 / PDF page 33, uses a subgroup containing the whole group center
and compact modulo it. *Discrete series II*, sections 7–8, printed pages
15–19, uses an actually compact subgroup with complementary noncompact
central directions. Its Theorem 1 proof on printed page 18 cites the
proof of Lemma 33 to infer analyticity of a smooth scalar separator.
The present matrix statement follows that local proof route using the
actual compact matrix Lie algebra and its full joint orbit. It is not a
verbatim restatement of the distribution lemma. It asserts no global
Cartan decomposition for general linear groups or a bridge between their
connected components.

A proof of this concrete statement still needs the actual
central-plus-compact Cartan operator, a polynomial annihilator,
identification and ellipticity of the polynomial differential operator
with analytic coefficients, and analytic elliptic regularity in the
actual matrix coordinates. Separate construction drafts or compilation
of the present proposition do not establish any of those obligations.
This module defines the statement only; an exact-target proof must follow
independent publication. Analytic jet uniqueness, propagation of zero
values, Lie-orbit density, admissibility, convolution reproduction and
automorphic differential growth remain separate assertions.

The retained registered sources are:

- Harish-Chandra, *Two theorems on semi-simple Lie groups*, Annals of
  Mathematics 83 (1966), section 16 and section 17, Lemma 33;
  source `provided-3315156dfd5120bb69df4005d1cb66c074532e8f8ab3cd2459c5990658370e91`,
  SHA256 `aff3875a87ea64bb7acc14aab723ba8fe665b79ad89ef19ecf90e0445a9cce2c`.
- Harish-Chandra, *Discrete series for semisimple Lie groups II: Explicit
  determination of the characters*, Acta Mathematica 116 (1966),
  sections 7–8, especially the proof of Theorem 1 on printed page 18;
  source `harish-chandra-1966-discrete-series-ii`,
  SHA256 `3ad72529bddbfe96e537bc3f49df6aa3223169c2abbe265d858c32c48545f3d9`.

Worker 94 prepared this statement specialization after rereading these
passages and the published differential-growth source audit. Worker 116
checked the actual imported carriers, reread the cited original passages,
visually checked the product-algebra hypotheses and square-sum construction,
and made the exact internal specialization explicit here.
