# Actual subgroup coroots selected by a supplied coweight

This internal comparison uses one actual commutative group scheme `T`
embedded by `i` in an affine group `G` and by `iH` in an affine group `H`
over any field `k`. A homomorphism `j : H → G` satisfies `iH ≫ j = i`.
The map `i` is a closed immersion, `T` is split, and `G` is locally of
finite type. The field and the two root-index types have independent
universes. No maximality, reductivity, reducedness, finite root-index
type, or simple connectedness is assumed.

The supplied actual root data `P` and `R` describe `i` and `iH` on the
unchanged character and cocharacter lattices of `T`. The supplied
coweight `ν` satisfies the explicit root comparison
`relativeRoots iH = {α | α ∈ relativeRoots i ∧ latticePairing T α ν = 0}`.
In an intended centralizer application this is the same coweight descended
from the original field. This module preserves it rather than selecting
a second coweight or a root base.

`IsRootDatumOf.root_range_eq_coweight_zero` rewrites that comparison with
the two actual-root-datum predicates. The resulting equality is
`range R.root = P.root '' {p | P.root' p ν = 0}`. This first theorem only
needs the actual data and the root comparison; it does not use splitness,
closedness, the factorization, or local finite type.

`IsRootDatumOf.coweightSubgroupRootEmbedding` uses the published finiteness
of the full actual Weyl image of a closed split torus in an affine group
locally of finite type. The root comparison gives root-support inclusion.
Together with the actual factorization, this permits direct application
of `IsRootDatumOf.sameTorusSubgroupEmbedding`. Its integral coroot
comparison uses actual normalizer reflections and finite Weyl-image
uniqueness. Thus the returned embedding preserves both roots and coroots.

`IsRootDatumOf.corootSpan_eq_coweight_zero` combines this embedding with
the root-range equality to identify `R.corootSpan ℤ` with the integral
span of `P.coroot '' {p | P.root' p ν = 0}`. It does not pass to rational
spans or claim that coroots generate the full cocharacter lattice.

`IsRootDatumOf.annihilator_iff_coweight_zero` identifies annihilation of
all `R` coroots with annihilation of all these ambient zero-root coroots.
Its proof puts the appropriate integral span in the kernel of
`P.toLinearMap x`, rewrites by the span equality, and uses the equality of
both actual pairings with `latticePairing T`. This equivalence holds for
every character `x` in the full actual character lattice.

The provenance is this internal deduction from the imported actual
same-torus coroot comparison and finite Weyl-image theorem. The module
does not construct either root datum, the supplied coweight, its Galois
fixedness, the root-zero comparison, a cocenter quotient, or the image of
its character pullback. Those geometric inputs remain necessary in the
unconditional Levi cocenter root-model proof.
