# Recovered integral root points and nonnegative restricted depth

This internal supporting unit compares actual lower integral root points with
the torus-then-field restricted depth in a supplied upper KP apartment. It
composes the full point-fixer comparison with exact integral-model recovery;
it does not construct the required models or prove the unconditional
depth-zero opposite-factor statement.

Supply a nonarchimedean local field `F`, its inertia fixed field `K`, a
smooth affine group scheme `G` over `F`, and actual lower and upper relative
component models `L` and `E` with `UnramifiedComponentModelRecovery L E`.
Supply a split torus `S` embedded in `G`, a commutative group scheme `T`
over `F` whose base change is a maximal split torus in connected reductive
`G_K`, a factorization `S → T → G` of the embedding of `S`, upper opposite
factor pairs, a KP apartment datum `D` for that upper torus and the actual
unramified integer valuation, and `x : D.Apartment`. Assume that
`E.full.integralPoints` equals the intersection of the character valuation
kernel with the pointwise fixer of the image of `{x}`.

`nonnegative_restrictedDepth_of_mem_full_integralPoints` proves that an
actual lower root point integral in `L.full` has nonnegative restricted
depth at `x`. Exact full recovery puts its scalar extension in the upper
full integral image, hence in the full point fixer of `x`. Scalar
extension also preserves its original root subgroup. The theorem
`KPApartmentData.restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero`
puts this extended point in the canonical restricted depth-zero subgroup.
The exact filtration-preimage theorem
`rootFiltration_torusFieldRestrictedRootFunctionFamily` reflects this
membership to the original lower field, yielding the claimed inequality.
No centralizer datum or V6 compatibility is needed for this direction.

`nonnegative_restrictedDepth_of_mem_neutral_integralPoints` follows by
the actual inclusion of the neutral model in the full model. On also
supplying an upper centralizer datum `C` and V6 compatibility, the theorem
`mem_neutral_integralPoints_iff_nonnegative_restrictedDepth` combines this
direction with
`mem_neutral_integralPoints_of_nonnegative_restrictedDepth`. Thus neutral
integrality and nonnegative restricted depth are equivalent for each
actual lower root point.

`rootGroupPoints_inf_neutral_integralPoints_eq_restrictedDepthZero`
expresses this equivalence as equality of subgroups of the original
`G(F)`: the intersection of its root group and neutral integral image
equals the inverse image of the canonical upper restricted depth-zero
subgroup. `neutralRootIntegralEquivRestrictedDepthZero` is the induced
multiplicative equivalence; its `_coe` theorem states that it preserves
each ambient generic point.

The provenance is the internal composition of the named root-fixer,
filtration-preimage, exact-recovery and nonnegative-integrality results.
The construction is at arbitrary universe `u`. It does not require a
lower root-datum valuation, a lower apartment, maximality of `S`, Galois
fixedness of `x`, or a neutral fixer-image equality. Actual model
existence, nearby parabolic model comparisons and radical nonvanishing
at value zero remain separate obligations.
