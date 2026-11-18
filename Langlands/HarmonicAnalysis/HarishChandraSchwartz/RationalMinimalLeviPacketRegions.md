# Cartan regions for the wave-packet estimates

This derived comparison uses the actual minimal Levi, the source-normalized
map `rationalMinimalH0`, and the existing ambient valuation coordinates.
The choice of simple roots attaining the maximum follows Waldspurger's
Proposition VI.3.1 proof, printed pp. 302–305. On the region where these root
values control the central coordinates, the comparison below places the
original point directly in the positive-part decay region. [Waldspurger (2003)](https://doi.org/10.1017/S1474748003000082)

`rationalMinimalSimpleRootSize` is the finite maximum of the absolute values
of the actual simple-root evaluations at `H₀(m)`, with value zero when
there are no simple roots. The equality
`eval_torusCharacterRestrict_rationalMinimalH0` identifies evaluation of a
restricted ambient rational character with its integer valuation at the
same group point `m`. It uses the character normalization of the actual
minimal-Levi valuation and the composition law for restriction.

`exists_rationalMinimalH0_seminorm_le_simpleRootSize_add_coordinates`
bounds any seminorm of `H₀(m)` by a constant times the root size plus the
norm of the ambient central coordinates. The relative roots together with
restricted ambient rational characters span the rational character space,
and the simple roots span the relative root part. Scalar extension gives
the corresponding real spanning statement. The proof propagates the
individual bounds along real linear combinations, uses the perfect
character and cocharacter pairing to bound the coordinates in a finite
basis, and uses the seminorm triangle inequality over that basis. The
constant is independent of `m`.

`exists_rationalMinimalLevi_packetRegions` gives one `δ > 0` for all real
thresholds `t`. For every point of the closed minimal-Levi chamber, with
root size `R` and central coordinate norm `Z`, either
`R ≤ max 1 t * (1 + Z)` or the roots attaining `R` are a nonempty set.
In the second case the proof takes the complementary simple roots as the
index of a proper standard Levi. Every outside simple root has evaluation
`R ≥ t`. Since `Z ≤ R` and `N(H₀(m)) ≤ C * (R + Z)`, the same roots all
satisfy `δ * N(H₀(m)) ≤ R` for `δ = (2 * C)⁻¹`. This gives membership in
both the threshold and positive-part regions at the original point.

`exists_rationalMinimalLevi_height_or_packetRegions` uses the existing
minimal-Levi Cartan height comparison when `N` is positive definite.
It retains the compact subgroup and the minimal-Levi covering at that
subgroup as premises. The first branch then has
`1 + rationalHeight ρ m ≤ D * (1 + Z)`, with `D ≥ 1` depending on `t`
and the structural and height data. This is the comparison needed to
apply central Fourier decay on that branch. The other branch supplies
the hypotheses for the threshold and positive-part estimates. Bounds
for the actual constant terms are separate inputs to the packet proof.
