# The split Cayley automorphism group is pinned split of type `G₂`

Author: Worker 161.

`Langlands.GroupScheme.SplitCayleyAutomorphismPinningStatement` is a
proposition. This module only states it. It is proved as
`Langlands.GroupScheme.splitCayleyAutomorphismPinning` in
`Langlands/GroupScheme/Composition/SplitCayleyAutomorphism/Pinning.lean`
(see `SplitCayleyAutomorphism/Pinning.md`). It is quantified over every
field `K` at universe `u`, in every characteristic, including two and three. Its subject is the
actual group scheme `(CayleyDatum.split K).automorphismGroup`. This is the
closed subgroup scheme of `GL₈` over `Spec K` whose points over every
`K`-algebra are the invertible matrices fixing the identity `(1, 0, 0, 1)`
and preserving Zorn's vector-matrix product. Both are constructed in
`Langlands/GroupScheme/Composition/SplitCayley.lean` and
`Langlands/GroupScheme/Composition/CayleyAutomorphismGroup.lean`.

For each `K` the proposition asserts two conclusions.

1. `center (CayleyDatum.split K).automorphismGroup = ⊥`. Here `center` is
   the Library's scheme-theoretic centre in
   `Langlands.GroupScheme.Rational.Characters`, a subgroup functor on all
   test schemes. A point `g` over `T` is central when every restriction of
   `g` along `T' ⟶ T` commutes with every point over `T'`. The conclusion
   says that only the identity point is central over every test scheme,
   nonreduced ones included.
2. There is an actual `SplitPinning` of the group, from
   `Langlands.GroupScheme.Reductive.Pinning`. Such a pinning contains a
   proof that the group is connected reductive, a split maximal torus, its
   actual root datum with a base, and root vectors for the simple roots.
   The coroots of this root datum span the full cocharacter lattice
   (`p.rootDatum.corootSpan ℤ = ⊤`), so the group is simply connected. Some
   numbering `e` of the simple roots by `Fin 2` makes every pairing of
   simple roots `p.rootDatum.pairing a b` equal to the entry
   `CartanMatrix.G₂ (e a) (e b)` of Mathlib's Cartan matrix
   `!![2, -3; -1, 2]`.

The first conclusion makes the group adjoint as well. It is stated
separately because it is the property a later reduction uses: inner forms
of this group are classified by cocycles in the group itself.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
Theorem 25.14, printed p.360 / PDF p.383, states that a split simple group
of type `G₂` is simply connected and adjoint, and is isomorphic to
`Aut_alg(𝒞)` for a split Cayley algebra `𝒞`. It refers to Springer for
arbitrary fields. Section 33.C, printed p.462 / PDF p.485, restates that
the automorphism group of the split Cayley algebra over any field is a
split simple group of type `G₂`. The statement here is a derived,
pinned form of these results, applied to the concrete Zorn model. Theorems
33.17 and 33.19 and Proposition 33.23 (printed pp.459–461 / PDF
pp.482–484) identify that model with the source's split Cayley algebra
`CD(M₂(F), -1)`. That argument is recorded in `SplitCayley.md` and is not
needed to state the proposition.

In the source, "simply connected" gives the full coroot span and
"adjoint" gives the trivial centre. "Simple of type `G₂`" gives the
Cartan matrix up to numbering of the two simple roots. Mathlib's
`pairing a b` evaluates root `a` on coroot `b`, which is the convention
of the Library's `TitsIndexData.cartan`. Mathlib's `CartanMatrix.G₂` has
`-3` in position `(0, 1)`, and a long root evaluates to `-3` on the
coroot of the short simple root. So `e` sends the long simple root to `0`.
This module proves nothing; it only states the proposition. The proof is
`splitCayleyAutomorphismPinning` in `SplitCayleyAutomorphism/Pinning.lean`.
