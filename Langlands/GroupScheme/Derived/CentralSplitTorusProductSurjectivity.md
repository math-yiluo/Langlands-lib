# Surjectivity of supplied split factors from a central Weyl norm

Author: Worker 1562.

This internal construction and its auxiliary theorems give a conditional
surjectivity reduction for the supplied derived and central split-product
problem. They do not prove the exact product-isogeny proposition:
unconditional centrality of the Weyl norm, or existence of the actual root
reflections used to obtain it, remains a structural obligation.

For any field `k`, commutative group scheme `T`, and group scheme `G` over `k`,
let `i : T → G` have monomorphic underlying scheme map. No affineness,
smoothness or reductivity is assumed for the first three results.
`relativeWeylTorusAction_sub_id_eval_mem_derived` proves that every actual
relative Weyl automorphism minus the identity has image in the actual derived
subgroup on all test schemes. Represent a Weyl class by a rational normalizer
point. The published `torusCommutatorEnd` evaluation formula identifies the
ambient value of this difference with its commutator with that point.
`derivedSubgroup_containsCommutators` supplies membership.

When the actual quotient `relativeWeylGroup i` has a finite enumeration,
`relativeWeylTorusComplement i` is the sum of the identity minus each Weyl
automorphism. `relativeWeylTorusComplement_add_norm` proves that this complement
plus `relativeWeylTorusNorm i` is the integer group-order multiple of the
identity. `relativeWeylTorusComplement_eval_mem_derived` proves that the
complement is derived-valued: evaluation turns its sum into a product, and each
factor is the inverse of a derived-valued commutator. These are actual
morphism and all-test statements, including nonreduced tests.

The power-factorization results assume an affine structure morphism for `G`, an
actual derived inclusion `d : D → G`, a split-subtorus inclusion `i : S → G`, a
maximal split torus `j : S_D → D`, and a morphism `e : S_D → S` satisfying
`j ≫ d = groupHom e ≫ i`. They also assume a split component `a : A → G` and
`c : A → S` with `groupHom c ≫ i = a`. For endomorphisms `q` and `r` of `S`
summing to `n` times its identity, assume that `q` is derived-valued on every
test scheme and that `groupHom r ≫ i` is central on all tests.
`exists_splitProduct_powerFactor_of_central_complement` then constructs an
actual map from `S` to `S_D × A` whose composite with the supplied product
`prodHom (groupHom e) (groupHom c)` is multiplication by `n`.

The proof factors `q` through `S_D` using
`IsDerivedSubgroup.exists_factor_splitTorusEnd`. It factors the central map
`r ≫ i` through `A` using `IsSplitComponent.exists_factor`. Monicity of `i`
identifies the latter factor's composite with `c` as `r`. The categorical
product lift of the two factors gives the required map; evaluation on every
test scheme verifies its composite as the sum `q + r`.

If `n` is nonzero, `splitProduct_surjective_of_central_complement` proves
scheme surjectivity of the supplied product. The published nonzero-integer
multiplication theorem gives surjectivity of its composite with the constructed
map, and `Surjective.of_comp` gives surjectivity of the product itself. This
conclusion concerns underlying schemes and does not assert surjectivity on
rational points.

`splitProduct_surjective_of_central_weyl_norm` specializes this argument to the
complement and norm, assuming a monomorphic `i`, a finite enumeration of the
actual relative Weyl quotient and centrality of the norm. Its order is nonzero
because a group is nonempty. No restriction on the characteristic is needed.

Finally `splitProduct_surjective_of_relative_reflections` assumes that `G` is
connected reductive and that `i` is maximal split, instead of separately
assuming ambient affineness, monicity or Weyl finiteness. It retains the
explicit premise that every actual relative root has an actual Weyl reflection
satisfying `IsRelativeReflection`. The connected reductive hypotheses provide
affineness, smoothness and connectedness; the closed torus inclusion gives
monicity, and `IsConnectedReductive.finite_relativeWeylGroup` supplies the finite
enumeration. The published `relativeWeylTorusNorm_isCentral` then supplies the
centrality premise. No existence theorem for these reflections is proved here.

The complement and all reductions are internal derived content constructed from
the imported actual Weyl action, commutator, split-image, split-component and
power-map results by the arguments described above. Fields and universes are
unrestricted. Finiteness, flatness, local finite presentation and the full
central kernel of the product are separate obligations of the isogeny target.
