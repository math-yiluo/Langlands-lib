# The actual star action, relative simple roots and split rank

Source: J. Tits, *Classification of algebraic semisimple groups* (1966),
§2.3, printed p.39 (proceedings PDF p.44), and §2.5.1, printed p.40
(PDF p.45), with compatible orders as in §2.1, pp.38–39 (PDF pp.43–44).
Registered source `tits-1966-classification-algebraic-semisimple`;
SHA-256 `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.

Every declaration belongs to `Langlands.GroupScheme` and is an unproved
`Prop`-valued definition. The common hypotheses are an arbitrary field
`k : Type u`, an actual `k`-group scheme `G` with affine and
locally-finite-type structure morphism, and `d : TitsIndexData G`.
This datum includes actual semisimplicity, a maximal split torus `S`,
a maximal torus `T` over `k` containing it, the actual absolute based
root datum over `k_s`, and compatible absolute/relative positivity.
There is no local-field or characteristic restriction, including in
characteristic two; `u` is arbitrary. Rank zero and empty diagrams are
allowed.

`TitsIndexStarInvariantStatement` asserts, for every
`σ : SeparableClosure k ≃ₐ[k] SeparableClosure k` and every actual
simple vertex `a`, that `d.star σ a` has zero restriction exactly when
`a` does. Thus it is invariance under each element of the full Library
star action. It also gives invariance of the distinguished complement.
This is the invariance implicit in Tits's distinction between the
orbits in `Δ₀` and the distinguished orbits of §2.3.

`TitsIndexRelativeSimpleRootsStatement` makes both parts of §2.5.1
explicit. Its first conjunct says that two distinguished vertices
have the same actual character restriction to `S` exactly when an
absolute Galois element carries one to the other under the star action.
Its second conjunct supplies an equivalence
`d.DistinguishedOrbit ≃ simpleRelativeRoots d.splitInclusion d.positiveCocharacter`.
For every distinguished vertex, the character underlying the image
of its orbit class must equal its actual restricted root. This
condition fixes the comparison map, rather than merely asserting that
the two sets have the same size.

The relative simple roots on the right are the existing Library
definition: positive relative roots, for the specified generic
cocharacter, that are not sums of two positive relative roots. The
relative roots themselves are the nonzero weights of the actual
adjoint representation of `S` on `Lie(G)`. This includes potentially
nonreduced relative root systems. The target neither replaces relative
roots by orbit labels nor presumes the absolute-to-relative restriction
theorem as a proof. The equivalence also entails finiteness of the
actual simple relative roots, since its orbit domain is already finite.

`TitsIndexSplitRankStatement` asserts that both the number of
distinguished star orbits and the number of these actual simple
relative roots equal `splitRank G`, after casting their natural
cardinalities to `ℕ∞`. The Library's split rank is independently
defined as the supremum of dimensions of closed split subtori; it
is not defined here using the index. The rank comparison is the
semisimple-group consequence of the simple-relative-root
correspondence: the simple relative roots form a basis of the
rational character space of a maximal split torus. Tits §2.5.1
states the orbit correspondence and recovery of `S` from the
index; the precise comparison with the Library's supremum
definition is a derived formalization obligation. This equality
is asserted only for semisimple groups carried by the datum, so
a reductive group with a positive-dimensional split center is
not erroneously assigned its semisimple root rank.

`TitsIndexStarRelativeRootsStatement` is exactly the conjunction
of star invariance and the actual simple-root comparison.
`TitsIndexRelativeStructureStatement` is exactly the conjunction
of that target and the split-rank target. Both are at the same
arbitrary universe and add no hypotheses.

The remaining proof units are star invariance with the restriction/orbit
and actual-simple-root comparison, and the comparison with the
independent split rank. Published relative-root-system,
absolute-restriction and maximal-split-torus results may be used after
checking their exact hypotheses. The existence of their statement
definitions is not a proof of any target here. No local classification,
local-field anisotropic classification or Kneser–Tits input occurs in
these definitions.
