# The actual simple-root step in the Bruhat word argument

Author: Worker 1325.

This internal supporting unit specializes the generic word argument to the
actual rational root groups of the Library. It does not prove
`RootGeneratedCentralizerRankOneStatement`. The field and universe remain
arbitrary, and no reduced-root-system assumption is used. Throughout, `k`
is a field, `T` is a commutative group scheme, `G` is an affine group scheme
over `k`, and the underlying scheme map of `i : T.toGrp ⟶ G` is a
monomorphism. Write `U(ν)(k)` for the dynamic unipotent point subgroup and
`U_a(k)` for the actual root-subgroup carrier at the identity test object.

`HasSimpleRootUnipotentFactorization i ν` states that, for a simple root
`a`, any actual representative `n` of a reflection in `a`, and any
`u ∈ U(ν)(k)`, there is a factorization `u = q * x` with
`q ∈ U(ν)(k)`, `n * q * n⁻¹ ∈ U(ν)(k)`, and `x ∈ U_a(k)`.

`hasSimpleRootUnipotentFactorization_of_orderedRootPoints` proves this
predicate assuming genericity of `ν`, negation stability and finiteness of
the actual roots, linear independence of the simple roots after
rationalization, and `HasOrderedRootPointFactorization i ν`. It uses the
published enumeration of indivisible positive roots and swaps the simple
root to the last position. The last point factor is `x`; the product of
the preceding factors is `q`. Each preceding factor lies in a positive
root group, so `q ∈ U(ν)(k)`. The published
`pairing_weylAction_pos_of_isRelativeReflection` shows that the reflection
keeps these preceding roots positive. Conjugation carries the factors
into their Weyl-translated root groups, hence into `U(ν)(k)`, proving the
assertion about `n * q * n⁻¹`. This extracts the unipotent part of the
published parabolic factorization argument; it needs no parabolic
endpoint identity or generic-centralizer equality.

`mul_mem_rootGenerated_doubleCosets_of_simpleReflection` additionally
assumes `IsSplitTorus T.toGrp` and genericity of `ν`. It fixes an arbitrary
subgroup `M ≤ N(k)` and assumes the factorization predicate, actual
opposite-factor-pair existence, an actual simple-reflection representative
`n ∈ M`, and containment in `M` of the normalizing points in
`⟨U_a(k), U_{-a}(k)⟩`. It proves that left multiplication by `n` preserves
`U(ν)(k) M U(ν)(k)`. Splitness makes rationalization of the character
lattice injective, so the reflection identity on the rational root span
implies the actual equality `weylAction i n a = -a`. Consequently the
representative sends the opposite root group into the positive root
group. The preceding factorization gives the generic argument's factor `q`. Opposite pairs
give the nonidentity rank-one factorization, and genericity gives the
two-sign alternative for every middle point. The proof then applies
`Langlands.Group.RankOneBruhat.mul_mem_doubleCosets_of_rankOne`.

Provenance is internal composition of published Library results. All
geometric existence and root-system premises are retained explicitly.
