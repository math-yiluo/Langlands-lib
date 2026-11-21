# Square integrability of the restriction in Iwasawa coordinates

`Langlands.Global.inducedRestrictionMemLp` proves the published
`Langlands.Global.InducedRestrictionMemLpStatement` without changing its
hypotheses. For a form `φ ∈ A²_P`, the restriction `f(k,[m]) = φ(mk)`
belongs to `L²` for `inducedL2Measure`, the product of compact Haar
probability on `K` and the quotient of `μ_M` on `M(F) \ M(𝔸)`, weighted by
`β(y(m)) |m^{-2ρ_P}|`. The statement asks for `MemLp`, which includes both
almost-everywhere strong measurability and a finite `L²` norm.

## Implemented proof

1. The closed immersion `P → G` gives local finite type of `P`. The
   restriction in adelic Levi coordinates is continuous since `φ` is
   continuous. The left invariance of `φ` under `U(𝔸) M(F)`, applied in
   `InducedInnerProductIntegrable.form_rational_mul`, makes the restriction
   invariant under `M(F)` in the Levi variable.
   `LeftCosetSpace.continuous_out_of_invariant` thus gives continuity on
   the product with the quotient, even though the representative map
   itself is not asserted to be continuous.
2. Write the weighted measure as `μ₀.withDensity D`, with `μ₀` the
   unweighted product measure and `D` the nonnegative density obtained
   from `inducedWeight`. The density is measurable by
   `measurable_inducedWeight_out`. By `memLp_two_iff_integrable_sq_norm`,
   it suffices to integrate `‖f‖²` for this measure; continuity supplies
   the needed strong measurability up to null sets.
3. The with-density formula for the nonnegative integral replaces the
   weighted integral of the square by the integral for `μ₀` of
   `D · ‖f‖ₑ²`. Since `β ≥ 0`, this integrand is pointwise the extended
   norm of the complex function `(↑β(y(m))) · m^{-2ρ_P} · f(k,[m])²`.
   The latter function is integrable by the published
   `InducedInnerProductIntegrable.integrable_weightedSquare` theorem.
   That theorem uses the reductivity of the Levi and its split component
   from the root presentation, the retraction identity `l ≫ π = 𝟙 M`,
   and continuity and compact support of `β`. The resulting finite
   nonnegative integral gives the asserted `MemLp`.

## Provenance and scope

Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series* (2011), §2, p. 311, defines `A²_P` via the split-component
transformation law and a square-integrability condition modulo that
component. Arthur, *An introduction to the trace formula* (2005), §7,
p. 32, describes the inducing Hilbert-space norm in norm-one Levi
coordinates. Here the published weighted-square estimate already carries
out the split-component integration for the Library's weighted model.
This proof converts exactly that estimate to `MemLp` and adds the quotient
measurability argument. No normalization of the integral of `β` is required.
The Iwasawa compatibility hypothesis is retained from the statement but
is not used by the weighted-square estimate. This is the restriction
input to `imaginaryIntertwiningExistenceBridge`, not a proof of
intertwining unitarity or of the spectral transform.
