# Representing relative Levi subgroup images

Author: Worker 178.

This module defines a representing correspondence for the actual relative Levi
images and proves that a section supplies an actual Levi subgroup over the
original base. It does not construct a representing scheme or assert that any
section exists.

`RelativeLevi.ModuliRepresentation P X` consists of a bijection, on every scheme
test `T → S`, between actual `S`-morphisms `T → X` and
`LeviImage ((GroupScheme.baseChange T.hom).obj P)`. Thus the points parametrize
images of homomorphisms satisfying the existing `IsRelativeLeviSubgroup`, with
equality of all-test subgroup functors rather than of presentations. Its
naturality field identifies restriction along `a : T' → T` with actual subgroup
base change along `a.left` followed by the canonical comparison from the
iterated ambient pullback to `P_{T'}`. The field is an equality of subgroup
functors, using inverse image under the inverse of that comparison. It does
not add an assumed base-change stability theorem to the Levi predicate.

`pulledBackPoint P T g` is the actual morphism from the terminal `T`-scheme to
`P_T`, given by the pullback lift of `g` and the identity of `T`.
For an actual scheme action `ModObj U.X X`, `ρ.IsEquivariant r` states that
`ρ` takes `g • x` to the conjugate of the Levi image of `x` by `r(g)`, on
every scheme test. The conjugation here is the operation of `ModuliValue`,
whose range comparison identifies it with the actual inner conjugate of an
inclusion. The definition works for any supplied `r : U → P`; the torsor
theorem will separately assume that it is the relative unipotent radical.

Given a section `s : S → X` with `s ≫ X.hom = id`, `ρ.ofSection s hs` first
uses the representing bijection on the test `S → S`. This yields an actual
Levi image of `P` pulled back along the identity of `S`. It then applies
`LeviImage.mapIso (baseChangeIdIso P)`, whose ambient transport proof preserves
the original Levi predicate. `ofSection_exists_presentation` extracts an actual
`L → P` with that image and `IsRelativeLeviSubgroup`; the final lemma forgets
the image equality. This is a proved consequence of the correspondence and
canonical identity comparison, not a new existence premise.

Every geometric object has the same arbitrary universe `u`. The image types
and correspondence data may lie in `Type (u+1)` because the subgroup functors
test all `u`-small schemes; no geometric object is enlarged or resized.

The definitions and section lemmas are internal implementations of Brian
Conrad's *Reductive group schemes* (2014), Definition 5.4.2, p.174, and
Corollary 5.4.6, p.178. Source ID:
`conrad-2014-reductive-group-schemes`; SHA-256:
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The source defines `Lev(P)` on all scheme tests and represents it, compatibly
with the radical's conjugation action, by a radical torsor. The first part of
the proof of Corollary 5.4.8, p.179, uses a point of that torsor to obtain a Levi
subgroup. Here that last implication is implemented directly from the
representing correspondence. None of these geometric existence theorems is
proved by this module.
