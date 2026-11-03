# Assembling morphisms of actual root data

Author: Worker 1375.

This is an internal construction on the published character and cocharacter
lattices. Its inputs retain the root bijection and matching-coroot law as
explicit hypotheses. It does not prove those geometric properties for
central isogenies.

Let `P` be a root datum on the actual lattices of a commutative group scheme
`T`, and `P'` one on those of `T'`, over an arbitrary field `k : Type u`.
The root index types have independent universes `v` and `w`. Let
`t : T → T'` be an actual homomorphism. Assume that character pullback
`χ ↦ t ≫ χ` is a bijection from the range of `P'.root` onto the range of
`P.root`.

`RootDatumHom.rootIndexEquivOfPullback` identifies each root index with its
root in its range, uses this supplied bijection of ranges, and returns the
root index on the other side. The two root maps are embeddings, so the
range identifications are equivalences. The companion root formula is
`P.root (rootIndexEquivOfPullback … j') = t ≫ P'.root j'`.

`RootDatumHom.ofRootCoroot` further assumes that the pairings of `P` and
`P'` are the actual lattice pairings and that every matching pair of roots
has matching coroots:
if `t ≫ P'.root j' = P.root j`, then
`P.coroot j ≫ t = P'.coroot j'`.
It constructs a Mathlib `RootPairing.Hom P' P`. Its weight map is the
published `characterRestrict (groupHom t)` with integer linear structure;
its coweight map is the published `RealTorusSpace.cocharacterMapInt t`.
They act by `χ ↦ t ≫ χ` and `ν ↦ ν ≫ t`, respectively. Both formulas are
definitional and are recorded by the accompanying lemmas.

The transpose identity follows from
`⟨t ≫ χ, ν⟩ = gmEndEquiv k (ν ≫ (t ≫ χ))`
and associativity of composition, which identifies this integer with
`⟨χ, ν ≫ t⟩`. The root condition is the formula for the index equivalence.
The coroot condition applies the supplied coroot law at the inverse root
index. These are exactly the three compatibility fields of
`RootPairing.Hom`, with the coweight map in its contravariant direction.

The construction uses no reductivity, maximality, splitness, finiteness of
the root index types, reducedness, isogeny or separability hypothesis.
The explicit range-bijection and coroot-law inputs remain necessary.
It asserts neither injectivity on the full lattices nor an isomorphism
criterion. In the host central-isogeny proof those conclusions require
separate arguments, as do the two geometric inputs.
