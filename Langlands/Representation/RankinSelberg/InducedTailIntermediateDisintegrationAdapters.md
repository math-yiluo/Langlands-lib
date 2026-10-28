# Rank and density adapters for actual lower-block disintegration

Worker 318 implements internal adapters between the actual lower-block
quotient coordinates used by the intermediate-tail calculation and the
published measure-disintegration statement.

`upperUnipotentQuotientCongr_eq_cast` proves that the published homeomorphism
coming from a numerical equality of matrix ranks agrees pointwise with equality
transport of quotient points. After eliminating the equality, quotient
induction reduces this to the identity law for matrix reindexing.
`quotientMeasureRankCast` is equality transport of a measure with the Borel
structures fixed at both ranks. `map_upperUnipotentQuotientCongr` proves that
pushing a measure through that actual homeomorphism gives precisely this
transport. Eliminating the rank equality makes this the identity map law for
measures. The construction applies only to equal ranks.

`measurable_comp_upperUnipotentQuotientCongr` proves equivalence of Borel
measurability before and after composition with this homeomorphism.
`integrable_quotientMeasureRankCast_iff` proves equivalence of actual absolute
integrability against the transported measure and against the original
measure after composition. `integral_quotientMeasureRankCast` proves equality
of the corresponding complex Bochner integrals. The integral law also holds
without an integrability hypothesis, with the usual total-integral convention.
Each proof eliminates the numerical rank equality and reduces the actual
homeomorphism to the identity. Thus there is no normalization scalar in these
same-rank transport laws.

`compatible_quotientMeasureRankCast_iff` treats equality of JPSS indices
`m=n`, whose actual matrix ranks are `m+1` and `n+1`. Over any non-archimedean
local field it fixes the group, unipotent subgroup and quotient Borel
structures, retains right invariance of both normalized unipotent Haar
measures, and proves equivalence of compatibility before and after measure
transport. Equality elimination identifies the same normalized Haar
constructions; no uniqueness theorem or new quotient measure is assumed.

`quotientChart_eq_cast` identifies the intermediate-tail chart with equality
transport of the published lower-block chart. It retains the actual lower-left
matrix and triangular parameter; the only change is the numerical target-rank
expression `(n+1)+d=(n+d)+1`.

`quotientDensity_eq_lowerBlockQuotientDensity` equates the two actual densities:
`quotientDensity (normalizedAbsoluteValue T) n d` is
`lowerBlockQuotientDensity T (n+1) d`. Quotient induction reduces this to the
proved power-of-`ofReal` formula, with the same normalized determinant absolute
value and negative integer exponent `-d`.

Provenance is internal: these are equality and descent laws for the named
published constructions. They provide no proof of quotient disintegration or
of the unchanged closed intermediate-tail span theorem.
