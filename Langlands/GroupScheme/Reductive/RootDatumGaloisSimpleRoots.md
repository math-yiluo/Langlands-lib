# Ordinary Galois actions on simple roots of descended positive systems

This internal construction restricts the published ordinary Galois root-index
action to a supplied base whose positive roots are exactly the roots of a
descended torus map. It then transfers that action to any supplied finite
ordering of the simple roots.

For a root datum `P` with finite index type `J` and base `b`,
`RootPairing.Base.mem_support_iff_positive_indecomposable` proves that an index
belongs to `b.support` exactly when it is positive and its root is not a sum of
two positive roots. A simple root has integral height one, while two positive
roots have positive integral heights, which proves one implication. For the
other, Mathlib's positive-root induction under addition either finds a simple
root or writes the root as a sum of a positive root and a simple root. This
argument does not require the root datum to be reduced.

`RootPairing.Base.mem_support_equiv_iff_of_isPos` applies this characterization
to a permutation of root indices and an integral linear equivalence of the
root lattice. If the permutation transports roots by this linear equivalence
and preserves positivity in both directions, it preserves simple-root support.
The inverse implication uses the inverse permutation and injectivity of the
linear equivalence.

The group-scheme part works over arbitrary fields `k` and `E` in universe `u`
with an algebra structure `k → E`. The root index type has independent universe
`v`. Supply a commutative group scheme `T` over `k`, an affine group scheme `G`,
a map `i : T.toGrp ⟶ G`, and a finite-index root datum `P` for the actual
base-changed map, as expressed by `IsRootDatumOf`. Supply a base `b`, an affine
group scheme `H` over `k`, a map `j : T.toGrp ⟶ H`, and the equality of positive
root predicates

```text
b.IsPos a ↔ P.root a ∈ roots (baseChange(j)).
```

No inclusion, Borel property, or comparison between `G` and `H` is silently
assumed. The displayed identification is an explicit premise.

`IsRootDatumOf.galoisRootIndexEquiv_isPos_iff` uses that premise and the
published invariance of roots of any descended map from the same torus. This
positivity lemma itself needs no finiteness assumption on `J`.
`IsRootDatumOf.galoisRootIndexEquiv_mem_support_iff` then applies the
root-datum argument above, using the ordinary character-lattice Galois linear
equivalence. The result uses the ordinary action without a Weyl correction.

`IsRootDatumOf.galoisSimpleRootIndexAction` restricts the actual root-index
permutation to `b.support` and proves its identity and multiplication laws
from the existing action on all roots. Its `_root` theorem identifies the
resulting actual root with its ordinary Galois transform. Multiplication
acts by the right-hand automorphism first.

For any `e : Fin r ≃ b.support`,
`IsRootDatumOf.galoisOrderedSimpleRootAction` conjugates this action by `e`
and `e.symm`, producing a monoid homomorphism

```text
(E ≃ₐ[k] E) →* Equiv.Perm (Fin r).
```

Its `_apply` theorem says that applying `e` intertwines the two permutations.
Its `_root` theorem identifies the actual root attached to a permuted
coordinate with the Galois transform of the original actual root. This formula
also covers the empty simple support. The construction needs no Galois,
finite-degree, perfectness, or infinitude hypothesis on the extension.

The provenance is internal: Mathlib's root-base height and positive-root
induction lemmas prove the support characterization; the published
`RootDatumGaloisRoots` constructions supply the actual weight transport and
root-index action; Mathlib's permutation conjugation transfers the action to
an ordering. No new assertion from the original Steinberg literature is
claimed here.

For a quasi-split cross-section application, consumers still have to construct
the appropriate descended torus and positive-root map and prove the displayed
positive-root identification. They also have to compare them with a chosen
split pinning, construct compatible root parametrizations and normalizers,
and prove equivariance of the ordered product and its actual coordinate
pullback. The coordinate permutation by itself supplies none of those
existence or equivariance results, closed-image descent, or rational lifting.
