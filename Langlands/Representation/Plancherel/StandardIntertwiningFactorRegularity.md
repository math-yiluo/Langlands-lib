# Seed-product regularity for normalized intertwining factors

This is an internal measure-transport deduction for the supplied ordered
subgroup charts. Its application is the ordered complementary-unipotent
integration on printed p.279 / PDF p.45 of Waldspurger (2003), registered
source `waldspurger-2003-plancherel`. It does not supply the reductive charts
or the source's convergence theorem.

Write `K` for the actual nested copy
`(V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)` and `L` for
`W.subgroupOf U₂`. The existing normalized factors on `V` and `W` are
pushforwards of finite nonnegative real multiples of independent measures
`μK` and `μL`. No restriction of an ambient measure is taken.

`normalizedComplementProductHomeomorph` is the product of the canonical
continuous group equivalences from these actual copies to `V` and `W`.
It maps ordered pairs to ordered pairs; it does not multiply elements of `G`.
`normalizedComplementProductMeasure_eq_map` expresses the existing ordered
product measure as the pushforward of the two scaled seed measures by that
homeomorphism, using `Measure.map_prod_map` and S-finiteness of both seeds.

`intersectionNormalizedFactor_prod_regular` assumes regularity of the
genuine product `μI₁₀.prod μK` and S-finiteness of both measures. Its proof
first uses `Measure.prod_smul_right` to obtain regularity after the finite
scaling, then transports through the identity on the first factor times the
canonical equivalence `K ≃ₜ V`.

`normalizedComplementProduct_regular` assumes regularity of the genuine
product `μK.prod μL` and S-finiteness of both measures. The two scalar-product
identities express the scaled product as two finite nonnegative real
scalings of that regular product. Regularity transports through
`normalizedComplementProductHomeomorph`.

These regularity instances require the displayed Borel structures on the
individual spaces and both the original and transported product spaces.
They do not require compactness, a Haar nonzero condition, compatible Weil
measures or local product identities. Regularity of the genuine seed products
remains a hypothesis; no assertion that arbitrary products are regular is
made. Actual source normalizations, geometry, convergence, continuation and
the full Plancherel conclusions remain open.

`comp_hasIntegral_of_seedRegularity` applies the preceding independently
reviewed compact-open composition construction to the same measures and
actual integral witnesses. Its premises replace regularity of the two
constructed products by regularity of `μI₁₀.prod μK` and `μK.prod μL`,
respectively, with the two additional source-product Borel structures
explicit. Typeclass synthesis uses the two instances above; the proof then
calls `comp_hasIntegral_of_unitCompactOpens` unchanged.

In particular, all four genuine seed-product regularity premises remain:
`μH.prod μK`, `μI₂₁.prod μL`, `μI₁₀.prod μK`, and `μK.prod μL`. The
three supplied literal subgroup charts, three local compact-open product
identities, compactness of the five local subgroups, four unit-mass
identities, compatible Weil measures, closedness of the three `Uᵢ`, and
the earlier individual Haar, regularity, right-invariance, S-finiteness,
local compactness, separation and Borel hypotheses all remain. The
representation is the canonical `SmoothRep` over the common Levi, with
independent group and representation-carrier universes.

The integral theorem retains both actual `HasIntegral` witnesses, including
an actual intermediate induced section, and absolute ordered scalar
integrability on the constructed product for every smooth functional on
the original carrier. Its conclusion is the direct `HasIntegral` relation.
It neither proves arbitrary convergence and representability nor assumes
irreducibility of parabolic induction. It does not identify this conditional
relation with the continued rational-operator composition IV.1(12), printed
p.283 / PDF p.49. No full-task Plancherel condition is closed.
