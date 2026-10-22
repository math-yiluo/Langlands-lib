# Normalized block compression laws

Author: Worker 99.

The closing theorem `Langlands.Jacquet.blockCompression.{uF,uV}` proves exactly
`Langlands.Jacquet.BlockCompressionStatement.{uF,uV}` from
`Langlands.Representation.Jacquet.BlockCompressionStatement`.
`blockCompressedAction_mul` and `blockCompressedAction_mk` expose its
multiplicativity and quotient-compatibility clauses by name.

## Scope and conventions

All parameters of the published proposition are retained: the prime, the
independently sized p-adic field, its supplied topological data, every natural
rank and block shape, the independently sized complex module, the smooth
representation, and the actual compact open subgroup with the existing
`HasBlockIwahoriFactorization` hypothesis. Both scalar tuples in the first law
are weakly contracting. There are no additional hypotheses on dimension,
admissibility, nonzero carriers, ranks, shapes, or central scalars.

Write `A(a) = B.blockScalar F.Carrier a`, `e_K = Compact.averageMap ρ hρ K hK`,
and `N = B.unipotentSubgroup F.Carrier`. The compression is the published
endomorphism `v ↦ e_K (ρ(A(a))v)` of the actual `K`-fixed submodule. The
quotient map is the actual `Jacquet.mk ρ N`, and its action is the
unnormalized `Jacquet.action`. The quotient equality has no modulus, index,
or other scalar.

## Implemented proof

Two helpers work directly with the published finite-orbit definition
of `e_K`:

1. The public `map_averageMap_of_forall_eq` says that if a complex linear map takes every
   vector in the `K`-orbit of `v` to `w`, then it takes `e_K v` to `w`.
   Smoothness and compactness give a finite orbit. Linearity moves the map
   through the finite sum and its normalizing scalar. The orbit is nonempty,
   so its cardinality is nonzero in the complex numbers and cancels.
2. The private `average_apply_subgroup` proves `e_K (ρ(k)v) = e_K v` for `k ∈ K`.
   Multiplication by `k` and its inverse show equality of the two orbit sets;
   the actual `orbitMean` expressions are therefore equal.

The closing proof derives three local geometric facts. First, the accepted
commutation identity for block scalars in the product Levi passes through
`leviEmbedding`, so `A(a)` commutes with each element of `K ∩ M`. Second,
for `l ∈ K ∩ N⁻`, inverse lower containment gives
`A(a)⁻¹ l A(a) ∈ K`. Thus `ρ(l)` fixes `ρ(A(a))v` when `v` is `K`-fixed.
The Levi factors also fix this vector by commutation and the fixed-vector
condition.

Third, apply surjectivity of the given lower–Levi–upper product to `k⁻¹`.
Inversion writes `k = u⁻¹ m⁻¹ l⁻¹`. The preceding fixedness facts remove
the last two factors. Consequently every `K`-translate of `ρ(A(a))v` is an
upper-intersection translate of the same vector. Only surjectivity of the
assumed bijection is needed in this step; no extra factorization assumption
is introduced.

For multiplicativity, put `w = ρ(A(b))v` and apply the first averaging
helper to the linear map `f = e_K ∘ ρ(A(a))`. The geometric reduction
writes `ρ(k)w = ρ(u)w` with `u ∈ K ∩ N`. Upper containment gives
`A(a)uA(a)⁻¹ ∈ K`; the second averaging helper removes its action after
moving it through `ρ(A(a))`. Hence `f` is constant on the `K`-orbit of
`w`, proving `e_K ρ(A(a)) e_K ρ(A(b))v = e_K ρ(A(a)A(b))v`.
The block-scalar monoid homomorphism and extensionality give the required
endomorphism equality, with composition in the stated order.

For quotient compatibility, use the first helper with `f = Jacquet.mk ρ N`
and `w = ρ(A(a))v`. The same geometric reduction leaves an action by an
element of `N`, which the published `mk_apply_subgroup` removes.
`action_mk` identifies the resulting quotient with the unnormalized
Levi action in the target.

## Provenance

This is an internal derivation from the published compact finite-orbit
average, block factorization predicate and coinvariant quotient. The two
short finite-mean arguments use the elementary method already present in
private helpers of the published
`Langlands.Representation.Smooth.Contragredient.CompactDualityProof`;
that module and all existing imported pairs remain unchanged.

The motivating original is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, registered as
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained source is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
Pages 3–6 were read: section 3 gives the quotient and normalization, section 4
states factorization, and III.5.1–III.5.3 give the motivating coset-sum laws.
No project errata file for this source was present in the current Library.

The implemented proof uses the supplied weak-chamber containments directly.
It does not invoke Casselman's coset-sum identities as a theorem about the
normalized average. It constructs no averages on radical intersections,
uses no Haar-modulus or subgroup-index comparison, and asserts no
stabilization, contraction limit, or canonical-lift theorem.
