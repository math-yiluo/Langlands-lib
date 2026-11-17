# The padded Whittaker gauge bound for actual cuspidal realizations

The theorem `unequalPadGauge` proves the unchanged published proposition
`Langlands.Global.RankinSelbergGlobal.UnequalPadGaugeStatement`, with its
universe and all of its hypotheses retained.

Fix an actual cuspidal realization and a proper padded block of size `t+1`.
The published cusp bound supplies a common determinant exponent `beta` for
all realized vectors. Put
`A = 3 + sum_j (j+1)*(t-j)` and choose
`C = max(0, A-beta)`. This nonnegative threshold depends on the realization
and block rank, and is chosen before the standard additive character and
vector.

For `sigma > C`, one has `beta+sigma > A`. The compact torus bound for the
actual padded cuspidal Whittaker integrand therefore applies uniformly over
every compact set of right translates. Its inverse diagonal Haar modulus
has exactly the root exponents `-((j+1)*(t-j))`, so its hypothesis is the
displayed inequality.

The integrand is measurable and its extended norm is left invariant under
the smaller group's adelic upper unipotent subgroup. The actual Whittaker
quotient criterion converts these compact-uniform torus bounds into
finiteness for the Library's `whittakerQuotientMeasure`, evaluated at the
chosen quotient representatives. Unfolding the integrand gives exactly the
integral in `PadWhittakerGaugeBound`. No statement or imported statement pair
is changed.

The cusp exponent is supplied by
`CuspCentralBound.exists_norm_cuspFunction_le`. The proof uses the
realization's actual cusp space, its linear equivalence with realized
vectors, and its published Whittaker decay class to specialize the
compact-uniform diagonal estimate.

The criterion is
`WhittakerCompactTorusIntegral.lintegral_whittakerQuotient_lt_top_of_compactTorusBound`.
It identifies the defined Whittaker-quotient integral with the ambient Haar
integral over its rational-unipotent fundamental domain. The actual
diagonal–unipotent–compact factorization, compact-uniform inverse-modulus
torus bounds and finite unipotent covolume then give finiteness. The present
proof chooses canonical Haar on the full finite idele torus; the imported
estimates and criterion permit any Haar normalization.

The proof is an internal composition of these imported compact torus,
Haar modulus, cusp-space and quotient-comparison results. It introduces no
additional premise on the realization, character, vector or number field.
