# Comparison of opposite-root components and depth sums

This module contains internal consequences of the Library's actual root
subgroups, dynamic opposite-cell injectivity, and apartment translation action.
It applies over any field `k`, without local compactness or a discrete valuation.

For an affine group scheme `G`, a split torus `S`, a homomorphism `i : S → G`,
and a nonzero character `a`, `oppositeRootTripleProductEmbedding` embeds the
product `U_{-a}(k) × Z × U_a(k)` in `G(k)` by multiplication. Here `Z` may be
any type equipped with an injective map into the actual centralizer of `i`.
The underlying injectivity theorem
`oppositeRootTripleProduct_injective_of_isSplitTorus` chooses an integral
cocharacter with positive pairing against `a`, using
`IsSplitTorus.exists_pairing_eq_pos`. The positive and negative root
subgroups lie in the corresponding opposite dynamic unipotent subgroups by
`RelativeRoot.subgroup_le_dynamicUnipotent`. The existing
`unipotentTripleProduct_injective` then applies. Its proof uses opposite-cell
injectivity and uniqueness of dynamic limits.

For a representative `C : CentralizerDatum i` of the actual torus
centralizer, `centralizerComponent_eq_of_root_factorizations` says that any
two products `v' j(z) v = w' j(t) w` with the displayed opposite-root outer
factors have `z = t`. The centralizer inclusion is a monomorphism, so it is
injective on rational points. The theorem applies the preceding product
injectivity and projects to its central coordinate. It needs no assertion
that an arbitrary ambient point admits such a factorization.

`RootFunctionFamily.opposite_value_sum_vadd` proves that translating a root
function family leaves `φ_a(g) + φ_{-a}(h)` unchanged. The two translations
are the real numbers `a(w)` and `-a(w)`, and cancel inside `WithTop ℝ`;
the calculation also covers infinite values. Consequently
`Equipollent.opposite_value_sum_eq` gives this invariance for equipollent
families, and `KPApartmentData.opposite_value_sum_eq` gives it for any two
points of the same supplied apartment.

These are derived comparison tools for the local coroot calculation. They
do not construct rank-one coordinates, compare a chosen apartment with a
Chevalley–Steinberg model, or prove the coroot-component target.
