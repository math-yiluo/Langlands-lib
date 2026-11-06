# Unique lifting of based-root-datum isomorphisms

Author: Worker 1472.

`Langlands.GroupScheme.PinnedIsomorphismStatement.{u}` defines a
proposition over every field `k : Type u`. It asserts no proof.

The inputs are actual group schemes `G` and `H`, their affine
instances, and pinnings `p : SplitPinning G` and `q : SplitPinning H`.
Each pinning includes actual connected reductivity, a split maximal
torus, a realized finite reduced root datum, a base, and linear
trivializations of the actual simple-root Lie spaces. Thus the group
and torus schemes and their Lie spaces are the published actual ones.

An input `e : RootPairing.Equiv p.rootDatum q.rootDatum` identifies
the integral root data. The additional hypothesis says that its
root-index bijection carries the support of the source base onto the
support of the target base. This is an isomorphism of based root
data, including the full character and cocharacter lattices and
their pairing. It is not restricted to the spans of the roots.

The conclusion is a unique `f : SplitPinning.Iso p q` with the
specified lattice and index maps. Such an `f` contains an actual
group-scheme isomorphism and an actual torus isomorphism, their
commuting inclusion square, the root and coroot equations, base
preservation, and equality of corresponding root vectors under the
actual linear differential. Uniqueness is equality of this whole
structure among lifts of the specified equivalence.

The directions of the maps are explicit. If `t = f.torusIso`, then
`characterLattice.congr t` sends `χ` to `t.inv ≫ χ`, so it is the
inverse of ordinary character pullback and agrees with
`e.weightEquiv`. The map `cocharacterLattice.congr t` sends `ν` to
`ν ≫ t.hom`. Mathlib's `e.coweightEquiv` runs from the target
cocharacter lattice to the source one, so the induced forward
cocharacter map agrees with `e.coweightEquiv.symm`. Both additive
lattice equivalences are viewed as `ℤ`-linear equivalences in the
equations. The root-index bijection of `f` is exactly that of `e`.

This is the full-faithfulness part of Conrad, *Reductive group
schemes* (2014), Theorem 6.1.17, printed/PDF p.197, specialized to
fields and expressed with inverse character pullback in the forward
direction. The theorem states an equivalence between pinned split
reductive groups and based root data using isomorphisms as morphisms.
Definition 6.1.1, p.186, supplies the pinning convention; Corollary
6.1.15, p.195, supplies faithfulness. The discussion preceding
Proposition 7.1.6, p.243, expresses pinning preservation for
isomorphisms by equality of simple-root vectors under the Lie map.
Inverting the character pullback convention only reverses an
isomorphism and does not restrict which isomorphisms can lift.

The formulation retains arbitrary fields and universe `u`, including
groups with a central torus and the empty-root case. It asserts no
existence of a group for an abstract based root datum, no general
isogeny theorem, no automorphism-group splitting over coefficient
algebras, and no descent or quasi-split inner-form existence.
