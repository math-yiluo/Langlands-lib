# Actual corank coefficients and entire specialization

Worker 486. This internal consumer combines the published corank entire-slice
theorem with the actual unramified Laurent kernel and packages the separate
second-block deformation proposition for coefficient-image vectors.

Write `T = F.canonicalTopologicalData`. `HasCommonCompactOpenRightLevel F U`
means that a single compact open subgroup fixes every function of `U` on the
right. `corankCoefficientFamily F ψ ν Wprime U` is the actual function

```text
c u m = sliceCoefficient T ν
  (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U u) Wprime 0) m.
```

The integer index is unrestricted. The deformation parameter is `u`; the
spectral variable of the integrand remains zero, including its corank
determinant shift by `-1/2`. All measures use the canonical Borel structures.
No support condition is included in this definition.

`corankCoefficientFamily_integrable_entire` applies the published closed
`corankOneEntireSlice` theorem. For the supplied compatible quotient measure,
any full inverse-character Whittaker-type representation on `GL_(r+1)`, any
functional and any vector of its actual coefficient image, a pointwise entire
family on `GL_(r+2)` with one compact open right level has integrable slices
at every parameter. The literal coefficient family is entire coefficientwise.
The proof just reorders the quantifiers of that theorem. The original field
and test-representation universes are independent, rank parameter zero is
included, and the functional and coefficient may be zero. Reducible full-type
representations remain allowed.

`corankCoefficientFamily_clearing_at_zero` supplies this proved entire
dependence to `spectralKernel_laurent_clearing_at_zero`. Its kernel is exactly

```text
(P0 * P1.comp (Polynomial.C (spectralPoint q u) * Polynomial.X)).toLaurent,
q = T.residueCardinality.
```

The conclusion says that `(P0 * P1).toLaurent` clears the actual original
slice series at parameter zero. Formal Laurent clearing on a real ray
`u > C` is still an explicit hypothesis. In particular, this theorem does
not derive formal coefficient identities from rational integral identities.

`secondBlock_whittakerFamily` retains
`TwoBlockSecondWhittakerDeformationStatement` as an explicit premise.
It takes the original ordered dependent blocks, their full standard-character
Whittaker type, a nonzero functional at zero, and any vector `W0` of its
actual coefficient image. Surjectivity of `modelMap` supplies an original
vector representing `W0`. Applying the premise produces the scalar family.
Its per-parameter functional/vector realizations prove standard Whittaker
covariance, so the same scalar functions define an actual family `U` of
`WhittakerFunctions`. The theorem retains those realizations through
`coefficientMap`, the single compact open level and pointwise analyticity.
Evaluation of the original `modelMap` equality proves `U 0 = W0.val` exactly.
No irreducibility or identification of parameter-dependent vector carriers is
used.

The provenance is internal composition of existing published interfaces.
The corank proof implements the common-support and finite-evaluation argument
motivated by JPSS (1983), Section 4.5, printed pages 408–409; the second-block
statement explains its separate transport from that section for the
second-block parameter used in Section 6.1, printed page 427. This module
introduces no new direct claim from the literature. It proves neither closed
adjacent-rank gamma or L target. The second-block proposition and formal
real-ray clearing remain inputs to their respective assertions.
