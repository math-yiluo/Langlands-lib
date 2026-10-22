# Real averaging prerequisites for quotient integration

Worker 112 formalizes three proposition definitions needed to prove the existing
`CompatibleMeasureExists` target. No proposition in this module is proved or
assumed by an instance. `RealQuotientMeasurePrerequisites` is their conjunction.
The final quotient-measure construction must consume independently proved
versions of these obligations.

## Original source and convention

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), section 2.6, Lemma 2.49 and Proposition 2.50, printed page 62 (PDF page
75), and the sufficiency proof of Theorem 2.51, printed page 63 (PDF page 76).
The averaging operation is equation (2.47), printed page 61 (PDF page 74).
Registered source: `folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The original PDF pages 74–76 were read for this formalization.

Folland uses right cosets `xH`, averages `f(xh)`, and left translation on the
quotient. The published project API uses left cosets `H*x`, the actual quotient
`LeftQuotient H`, and averages `f(h*x)`. Right invariance of the subgroup
measure therefore supplies independence of the representative. Our real-valued
integrals are the real restriction of the source's averaging operation. We use
the representative formula directly to avoid depending on a new averaging API.
The quotient topology and subgroup subtype topology are those already induced
by these types; neither is an arbitrary replacement topology.

## Exact statements

`RealQuotientCompactNormalization` says that for every compact set `K` in the
left quotient there is a real continuous compactly supported function `f` on
`G`, everywhere nonnegative, whose subgroup integral equals one at every
representative of every point of `K`. This is the real version of Lemma 2.49.

`RealQuotientPositiveLifting` says that every real continuous compactly supported
quotient function `φ` has a real continuous compactly supported lift `f` with
fiber integral exactly `φ` at every representative. The lift can be chosen
nonnegative whenever `φ` is nonnegative. This is the real specialization of
Proposition 2.50; its additional equality of support images is not needed here
and is not part of this weaker statement.

These two statements quantify over every locally compact Hausdorff topological
group and every closed subgroup. They require a Borel structure on the subgroup
and a regular Haar measure that is also right invariant. Mathlib's
`IsHaarMeasure` includes left invariance, finiteness on compact sets and positivity
on nonempty open sets. Thus this is a nonzero two-sided Haar measure. The
lifting results in the source need only one-sided Haar invariance in the
appropriate convention; the stronger two-sided assumption here is the one
available in the parent theorem. No ambient measure or quotient measurable
structure is needed for these two conclusions.

`RealAveragingKernelIntegralZero` says that if every subgroup integral of a
real continuous compactly supported function vanishes, its integral against the
supplied ambient measure is zero. It additionally requires a Borel structure
on `G` and a regular ambient Haar measure that is also right invariant. This
is the key claim in the sufficiency proof of Theorem 2.51, specialized to the
case of two-sided Haar measures on both groups. In this case the two modular
functions are trivial, so the source's modular compatibility requirement is
satisfied. The statement makes no assertion for arbitrary incompatible modular
functions. The analogous claim for `H*x` uses the reversed multiplication
convention throughout.

No second countability, sigma compactness, quotient measure, existence of a
positive functional, or version of the desired conclusions is a premise. The
universal group type has one unrestricted universe parameter. Every integral
is Mathlib's actual real Bochner integral. Fiber and ambient integrability
follow from the closed subgroup, regularity and compact support in the eventual
proofs; they are not used here to define a substitute integral.
