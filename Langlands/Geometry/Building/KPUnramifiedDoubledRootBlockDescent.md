# Conditional doubled-root block descent

This internal derived lemma concerns a supplied concrete unramified apartment
lift, a lower point, a relative root `a` whose double is also a root, and a
nonnegative real depth `r`. It assumes a closed representative `q : U → G` of
the actual doubled-root functor and a supplied smooth integral model of `U`
with connected special fibre. The model must identify its integral-coordinate
points over the maximal unramified extension with the inverse image under
`q` of the scaled doubled-root subgroup at depth `2r`, on every such point.
This model-existence and valuation-comparison hypothesis is not proved here.
`IsDoubledRootDepthModelAt` packages just the all-point lattice comparison;
smoothness, connected special fibre, closed representability and the
actual doubled-root hypothesis remain separate arguments of
`block_mem_rootFiber_of_doubledRootModel`.

The uniform upper restriction fibre factors as `x*z`, with `x` in the scaled
`a` subgroup and `z` in the scaled `2a` subgroup, both at depth `r`, by
`mem_rootFiltrationSpan_iff_exists_scaled_mul`. The doubled factor belongs
to the actual base-changed doubled-root functor. Base change of the supplied
representative therefore lifts it to a point of `U` over that extension.

The two scaled factors are Galois stable. Their intersection is exactly the
scaled doubled-root subgroup at depth `2r`, by
`scaledRootDepth_inf_double`. The model comparison consequently gives
`IsRationalIntersectionModel` for these two subgroups. The published
integral-coset descent theorem, through
`exists_rational_right_factorization_of_rationalIntersectionModel`, corrects
the lifted right factor and produces two actual lower-field rational factors
with their original upper subgroup bounds. The lower filtration is the exact
preimage of each scaled subgroup, by `filtration_eq_restrictedDepth`.
Thus the rational factors belong to `U_{a,y,r}` and `U_{2a,y,r}`, in that
order, and their product is the original rational point.

The argument needs only that the extension of the original rational point
belongs to the uniform upper fibre; it does not additionally assume membership
of the original point in the lower root group. It proves neither model
existence nor the unconditional root-comparison field. Its provenance is
composition of the stated companion depth lemmas, root-functor
representability and base change, and the rational integral-coset adapter.
There is no direct original-literature assertion.
