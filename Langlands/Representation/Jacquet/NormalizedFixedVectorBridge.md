# Compact fixed vectors in normalized Jacquet modules

This is an internal adapter for the actual intrinsic Haar-normalized Jacquet
functor. It makes no new assertion from the literature and does not prove either
VI.9.4 target. It retains the closedness, compactness, factorization and
compact-containment hypotheses used below.

`NormalizedJacquetBridge.normalizedFixedVectorsEquiv` is a complex-linear
equivalence between the vectors fixed by `K ∩ M` in the actual normalized Jacquet
module and those fixed by that subgroup in the unnormalized coinvariant action.
Here `G` is a locally compact nonarchimedean group, `N` is closed, `M` normalizes
`N` and is closed, and `K` is compact open. The existing
`NormalizedJacquetBridge.character_trivial` theorem proves that the intrinsic
normalizing character is trivial on `K ∩ M`. The definition first applies the
identity-on-vectors linear equivalence from
`fixedVectors_twist_eq_of_le_ker`, then restricts
`Jacquet.Localization.trivialEquiv` to fixed vectors. It therefore compares the
published localized normalized carrier and the published ordinary coinvariant
carrier, with no change of subgroup.

`nonzero_fixed_of_surjective` takes surjectivity of the actual unnormalized
`fixedJacquetMap` for a smooth representation `D`. It sends a nonzero normalized
fixed vector through this equivalence and lifts the result along that map. A zero
lift would have zero image, contradicting injectivity of the equivalence. No
finite-dimensionality assumption is used.

`normalized_generation` transports generation by `K`-fixed vectors in `A` to
generation by `K ∩ M`-fixed vectors in its normalized Jacquet module. It retains a
subgroup `K₀` normalizing `K` and the factorization `G = M N K₀`. The existing
algebraic `Jacquet.fixedVectors_generate_of_factorization` gives unnormalized
generation; `generation_of_equiv` transports it to the localized carrier.
Untwisting a subrepresentation, using compact character triviality, then proves
generation in the normalized action.

`bridge_of_surjective` combines these results with the existing
`normalized_isSubquotient`. Besides the hypotheses just listed, it assumes that
every finite subset of `N` is contained in a compact open subgroup of `N`, so
coinvariants preserve injections. For an actual subquotient `D` of `A`, it gives
normalized Jacquet generation, the actual normalized Jacquet subquotient
relation, and nonzero fixed-vector lifting. Surjectivity is supplied explicitly
for `D`; this adapter does not prove it. In particular, the definition does not
turn the conditional generalized Jacquet lemma into an unconditional result.

The group universe and representation-carrier universe remain independent.
There is no finite fixed dimension, admissibility, irreducibility, finite length,
or finite generation premise.
