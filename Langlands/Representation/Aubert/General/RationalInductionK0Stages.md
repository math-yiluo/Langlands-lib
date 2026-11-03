# Actual rational normalized induction stages on exact K0

This internal specialization combines `InductionK0Stages` with the actual
rational natural isomorphism `standardInductionStagesIso`. It retains the
literal standard rational-point subgroups, `pointTopology`, all standard
subsets, and independent universes `u` and `v`. Coefficient carriers have
universe `max (u + 1) v`.

`standardLeviInductionK0_of_preservation` is the full integer-linear map from exact finite-length
K0 of `levi i ν (leviIndex J I)` to that of `levi i ν J`. It uses the inclusion
proved by `levi_le_of_subset`, pulls back to the fine Levi's literal subgroup
copy, and applies normalized induction for
`isSemidirectDecomposition_in_levi`. Its finite-length preservation is supplied
for that exact restricted induction. Short-exactness is derived from
closedness of the ambient standard parabolic and radical, continuity of the
literal restricted Levi projection, and compact-open cofinality in the closed
coarse Levi. The rational point group is locally compact, nonarchimedean and
Hausdorff. The construction retains the named standard Levi intersection
statement, connected reductivity, maximal split torus and generic cocharacter.

The two stages theorems additionally retain a nonarchimedean local field,
`StandardCocharacterStatement`, continuous ambient standard projections, and
the compact-subgroup-limit conditions for the ambient and inner radicals.
`standardInductionK0_stages` states that coarse-to-ambient induction composed
with `standardLeviInductionK0_of_preservation` equals direct fine-to-ambient induction.
`standardInductionK0_comp_restricted` has domain the literal fine subgroup
inside the coarse Levi. Its right side first pulls back along the inverse
canonical subgroup equivalence and then applies direct fine induction.

Both results specialize the generic K0 descent using
`standardInductionStagesIso`. That isomorphism derives its positive Haar-modulus
product from `standardJacquetModulus_stages`; no stages equality or modulus
identity is an additional hypothesis here. Private preservation helpers
derive ambient and restricted short-exactness through
`normalizedInductionFunctor_preservesShortExact`, using exactly the supplied
finite-length preservation. No Jacquet finite-length assumption is required.
These are equalities of complete exact-K0 maps, including all virtual
finite-length classes.

The provenance is internal descent and specialization of the named existing
constructions. The geometric expansion, induced Weyl-conjugacy equation,
structural twisted-intersection properties and final Aubert induction equation
remain separate obligations.
