# Topology of a ring pullback spectrum

This internal helper module constructs the topological pushout used in the
assigned affine scheme pushout proof. Let `f : B →+* D` and `g : C →+* D`
be homomorphisms of arbitrary commutative rings in one universe. Write
`P = RingHom.pullback f g`, the subring of `B × C` of compatible pairs,
and let `i = f.pullbackFst g` and `j = f.pullbackSnd g` be its projections.

`comapPullbackCocone f g` is the cocone of actual continuous maps
`Spec B → Spec P` and `Spec C → Spec P` over `Spec D`, bundled in
`TopCat`. Its commutativity is the equality of contractions induced by
`RingHom.pullback_comm_sq f g`. When `f` is surjective,
`comapPullbackCoconeIsColimit f g hf` constructs a colimit witness, and
`isPushout_comap_pullback f g hf` records the corresponding `IsPushout`.
The target in this universal property is an arbitrary object of `TopCat`
in the same universe. No reducedness, nonzero-ring, or separation assumption
is used. The scheme universal property is a separate remaining part of
the host task.

## Covering the spectrum

`exists_comap_pullbackFst_eq` lifts a prime of `P` to a prime of `B`
when the kernel of `j` is not contained in that prime. Choose an element
`t` in that kernel outside the prime. Multiplication by its first coordinate
sends every element of `B` into `P` as `(t_B * b, 0)`. The inverse image
of the given ideal under this function is a prime ideal. The identities
`m(bc) * t = m(b) * m(c)` and `m(i(a)) = t * a`, together with
primality and `t` outside the prime, establish ideal closure, primality,
and the required contraction equality. This lemma needs no surjectivity.

If `f` is surjective, then `j` is surjective. The usual prime
correspondence lifts every prime containing its kernel to `C`.
Combined with the preceding lemma, this gives
`jointly_surjective_comap_pullback`.

## The quotient topology

`isOpen_iff_comap_pullback` proves that a subset of `Spec P` is
open exactly when its inverse images in both factor spectra are open.
The forward direction follows from continuity of contraction.
For the converse, consider a prime in the given subset.

If it is outside the image of `Spec C`, multiply the defining element
of a basic neighborhood in `Spec B` by an element of the kernel of `j`
outside the prime. The resulting element of `P` gives a basic neighborhood
whose inverse image in `Spec C` is empty.

If it comes from `Spec C`, choose a basic neighborhood `D(c)` there.
Write the closed complement of the open subset in `Spec B` as `V(I)`.
Commutativity on `Spec D` implies that `g(c)` belongs to the radical
of the image ideal `I.map f`. A positive power therefore belongs to that
image ideal. Surjectivity of `f` supplies an element `b` of `I` mapping
to that power, giving a compatible pair `(b, c^(n+1))` in `P`.
The corresponding basic neighborhood has both inverse images in the
prescribed opens. Joint surjectivity proves that it lies in the original
subset. This proves the reverse direction in both cases.

Consequently `isQuotientMap_comap_pullback` proves that
`Q = Sum.elim (comap i) (comap j)` is a surjective quotient map.

## Identifying the fibers and descending maps

`exists_comap_eq_of_comap_pullback_eq` shows that primes of `B` and `C`
with the same contraction to `P` come from one prime of `D`.
The equality of contractions forces the prime of `B` to contain the
kernel of `f`; prime correspondence and injectivity of contraction along
the surjective map `j` prove the claim.
`eq_of_comap_pullbackFst_eq` proves that contraction from `B` is injective
outside the image of `Spec C`, using the same kernel multiplication
argument as in the lifting proof. This latter lemma needs no surjectivity.
Since contraction along `j` is injective when `f` is surjective,
these results cover all pairs of points in a fiber of `Q`.
Thus `factorsThrough_comap_pullback` proves that any two functions
agreeing on `Spec D` are constant on the fibers of `Q`.

The colimit construction applies this fact to a compatible pair of
continuous maps. Choosing a preimage of each point under `Q` defines the
descended function; fiber constancy proves both factorization equations.
Continuity follows from the quotient-map criterion, because composition
with `Q` is the continuous disjoint-union map. Joint surjectivity also
proves uniqueness. This construction uses choice without assuming the
target is nonempty, so it covers empty spectra and empty targets as well.

## Provenance

These are derived internal constructions for the topology step in Stacks
Lemma 37.14.1, Tag 0ET0, as retained in the registered source
`stacks-affine-integral-scheme-pushouts-2026-11-06`. The elementary
prime-ideal and basic-open arguments above describe the implemented Lean
proof. The module imports Mathlib's pullback subring, spectrum topology,
and topological category infrastructure; it does not assume a scheme
pushout or modify the published scheme pushout statement.
