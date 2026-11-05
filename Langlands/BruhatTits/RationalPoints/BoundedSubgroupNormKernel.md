# Bounded subgroups and the actual rational norm kernel

These are derived topology adapters for actual affine rational points over a
nonarchimedean local field of either characteristic, at arbitrary universe `u`.
They use the canonical `rationalPointTopology` throughout.

`IsAlgebraicallyBounded.closure` extends a regular-function bound to the
topological closure. Evaluation is continuous and the scalar valuation bound
defines a closed ball, so its inverse image contains the closure.
`IsAlgebraicallyBounded.isCompact_closure` then applies the existing
`localFieldAffineBoundedCompactness_proof` to this closed bounded set.

`subgroup_le_rationalCommonNormKernel_of_isCompact_closure` uses the closure
as a subgroup of the canonical topological point group. Its compactness and
`compactSubgroup_le_rationalCommonNormKernel` put it, and therefore the original
subgroup, in the actual common kernel of rational norm characters.
The finite-type hypothesis supplies the existing point-group topology theorem.

`comap_le_rationalCommonNormKernel_of_isCompact_closure` treats an actual closed
immersion `j : H → G`. Its point map is a closed embedding. The inverse image of
the ambient compact closure is compact and closed and contains the closure of
the pulled-back subgroup. That subgroup therefore has compact closure in
`H(F)`, and the preceding result uses the rational characters of `H`.
The final theorem combines this with ambient algebraic boundedness.
Affineness of both group schemes and finite type of `H` are explicit; the final
theorem also requires finite type of `G` for the boundedness comparison.

The provenance is internal and derived from the existing affine
boundedness/compactness, closed-immersion point-map, and compact-subgroup norm
kernel lemmas. No additional numbered result in the literature is claimed.
In particular, these lemmas prove no boundedness assertion about building
fixers and no equality between a norm-one subgroup and a zero subgroup.
