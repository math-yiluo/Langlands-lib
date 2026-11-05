# Arithmetic model comparison

This internal result compares the actual completion-point images of a supplied
integral model with the fixed integral family from
`Langlands.Global.FiniteTypeIntegralFamily`. Let `F` be a number field in an
arbitrary universe, let `S` be a finite set of finite places, and let `M` be an
`IntegralModel` over the actual ring of `S`-integers, with its specified generic
isomorphism to `G`. The local subgroup is the existing
`IntegralModelCompletions.subgroup`, on the original coefficient-point carrier
`G.affinePoints (CommAlgCat.of F (FiniteCompletion F v))`.

`integerSubalgebra` equips the canonical completed integers at a place outside
`S` with the published `S`-integer action. Its underlying subring is exactly
`v.adicCompletionIntegers F`. The local scalar towers use the actual commuting
ring maps; no replacement field or valuation ring is introduced.

`mem_subgroup_iff` says that a coefficient point belongs to the local model
image exactly when every original-model regular function, restricted to the
generic fibre using `M.genericCoordinate`, has integral value at that point.
`mem_subgroup_iff_testSet` restricts this criterion to the fixed finite set
`integralPointTestSet` of original-model functions. These statements specialize
the arbitrary-section comparison and extension criteria in
`IntegralModel.BaseChangePoints`.

When `G.X.left` is affine, `eventually_uniform_integral` proves that for each
regular function `a` there is a cofinite set of places such that, at each place
outside `S` in that set, every point of the local model subgroup has integral
value on `a`. The exceptional set depends on `a`, not on the point. The proof
forms the `F`-subalgebra of functions with this property. Constants lie in it
because their diagonal finite adeles are integral almost everywhere; addition
and multiplication preserve it. Every `M.genericCoordinate` lies in it by
`mem_subgroup_iff`. The generation theorem
`M.adjoin_range_genericCoordinate_eq_top` then gives all generic regular
functions. The algebra homomorphism used for these closure arguments is
`GaloisPoint.coordinates`, whose values are the actual regular-function
evaluations.

`eventually_subgroup_le_representation` applies this uniform result to all
matrix entries and inverse entries of any one fixed finite-dimensional matrix
representation. Their finite conjunction gives eventual containment in its
linear integral subgroup; the representation need not be closed.

For affine finite-type `G`, `eventually_fixed_subgroup_le` applies uniform
integrality on the fixed finite-type family to the original model's finite
test set. Thus that family is eventually contained in the model image.
Combining this with the reverse containment for the chosen closed
representation proves `eventually_subgroup_eq`: outside a finite set, for every
proof that `v ∉ S`, the fixed family equals the local model subgroup.
`eventually_projection_mem` transfers eventual membership of each actual
finite adelic point, using the original restricted-product evaluation
coefficient map.

The results are derived from the cited internal APIs and the diagonal
restricted-product integrality property. They assume the supplied integral
model and its generic identification throughout. They do not construct good
models, prove integral maximality or parabolic covering, or establish the host
Iwasawa-family existence statement.
